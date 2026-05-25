/*
 *     The Certora Prover
 *     Copyright (C) 2025  Certora Ltd.
 *
 *     This program is free software: you can redistribute it and/or modify
 *     it under the terms of the GNU General Public License as published by
 *     the Free Software Foundation, version 3 of the License.
 *
 *     This program is distributed in the hope that it will be useful,
 *     but WITHOUT ANY WARRANTY; without even the implied warranty of
 *     MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *     GNU General Public License for more details.
 *
 *     You should have received a copy of the GNU General Public License
 *     along with this program.  If not, see <https://www.gnu.org/licenses/>.
 */

package sbf.tac

import analysis.*
import analysis.CommandWithRequiredDecls.Companion.withDecls
import analysis.opt.PatternRewriter
import analysis.opt.PatternRewriter.Key.*
import analysis.patterns.PatternHelpers
import com.certora.collect.*
import config.*
import datastructures.stdcollections.*
import instrumentation.transformers.*
import java.math.BigInteger
import log.*
import sbf.*
import sbf.cfg.*
import tac.*
import utils.*
import vc.data.*
import vc.data.SimplePatchingProgram.Companion.patchForEach
import vc.data.tacexprutil.*
import vc.data.tacexprutil.TACExprUtils.contains
import verifier.*
import wasm.analysis.intervals.IntervalBasedExprSimplifier

private typealias PI = analysis.PatternMatcher.Pattern<analysis.patterns.Info>
private typealias PatternHandlerContext = PatternRewriter.PatternHandler.Context

/**
    Used to annotate expressions whose results are guaraneed to fit in 64 bits.  The reason string is for debugging
    purposes only.

    Note: this really is treated as meaning the expression cannot overflow, except in the case of addition or
    subtraction of a constant that is a 2's complement representation of a negative number, which we accomodate by
    flipping the operation to subtraction or addition of the negation of that constant.
 */
val CANNOT_OVERFLOW_REASON = tac.MetaKey<String>("sbf.tac.cannot.overflow")

/**
    Attempts to minimize the use of the Mod operator in TAC expressions that implement 64-bit math using Bit256
    operations.
 */
object TACModSimplifier {
    private val optimistic = SolanaConfig.TACOptimisticOverflowOptimization.get()

    /**
        Transforms to be applied prior to loop unrolling.  We do this before unrolling because the unroller may have
        a better chance of guessing loop constants if we can eliminate the mod operations first.
     */
    fun CoreTACProgram.Linear.simplifyModMathPreUnroll() = runIf(SolanaConfig.TACSoundSignedMath.get()) {
        map(CoreToCoreTransformer(ReportTypes.MOD_MATH_NORMALIZE, ::normalize))
        .mapIfAllowed(CoreToCoreTransformer(ReportTypes.MOD_MATH_FIND_MORE_POINTERS, ::findMorePointers))
        .map(CoreToCoreTransformer(ReportTypes.MOD_MATH_REMOVE_NO_OVERFLOW, ::removeNoOverflow))
        .map(CoreToCoreTransformer(ReportTypes.MOD_MATH_SIMPLIFY, ::simplify))
        .mapIfAllowed(CoreToCoreTransformer(ReportTypes.MOD_MATH_INTERVALS_SIMPLIFY, IntervalBasedExprSimplifier::analyze))
    } ?: this

    /**
        Transforms to be applied after loop unrolling.  We do this after unrolling because we may have more visibility
        into the expressions, allowing for further simplifications.
     */
    fun CoreTACProgram.Linear.simplifyModMathPostUnroll() = runIf(SolanaConfig.TACSoundSignedMath.get()) {
        mapIfAllowed(CoreToCoreTransformer(ReportTypes.MOD_MATH_SIMPLIFY, ::simplify))
    } ?: this

    private val bvMode = Config.Smt.UseBV.get()

    private val modulus get() = modz64.modulus
    private val maxSigned get() = modz64.maxSigned
    private val BigInteger.inBounds get() = with(modz64) { inBounds }
    private fun Int.to2s() = with(modz64) { to2s() }
    private fun BigInteger.from2s() = with(modz64) { from2s() }

    private fun TACExpr.cannotOverflow(): Pair<String, TACExpr>? =
        (this as? TACExpr.AnnotationExp<*>)
            ?.takeIf { it.annot.k == CANNOT_OVERFLOW_REASON }
            ?.let { it.annot.v as String to it.o }

    context(PatternHelpers)
    private fun PI.mod() = this.rem(c(modulus))

    context(PatternHandlerContext)
    private fun TACExpr.mod() = this.mod(modulus.asTACExpr)

    context(PatternHelpers)
    private fun PI.signExtend() = c(7).signExtend(this)

    context(PatternHandlerContext)
    private fun ToTACExpr.isNeg() = this gt maxSigned.asTACExpr
    context(PatternHandlerContext)
    private fun ToTACExpr.isNonNeg() = this le maxSigned.asTACExpr
    context(PatternHandlerContext)
    private fun sameSign(o1: ToTACExpr, o2: ToTACExpr) = o1.isNonNeg() eq o2.isNonNeg()

    private fun CoreTACProgram.cleanup() = removeUnusedAssignments(this, expensive = false)

    /**
        Unfolds expressions that we will need to analyze, and normalizes expressions over constant negative values
        to use constant positive values instead (so they are less likely to overflow).

        This transform must be applied before the others from [TACModSimplifier].
     */
    private fun normalize(code: CoreTACProgram): CoreTACProgram {
        /**
            To avoid overflow (which is hard for solvers), we detect cases where we are adding (or subtracting) a
            constant that is a 2's complement representation of a negative number, and flip the operation to subtract
            (or add) the negation of that constant.
        */
        fun maybeFlipSign(encoded: BigInteger) =
            encoded.takeIf { it.inBounds }?.from2s()?.takeIf { it < BigInteger.ZERO }?.let { -it }

        return PatternRewriter.rewrite(
            ExprUnfolder.unfoldAll(code) { e ->
                e.rhs.contains {
                    it is TACExpr.BinOp.Mod ||
                    it is TACExpr.BinOp.BWAnd ||
                    it is TACExpr.BinOp.ShiftRightLogical ||
                    it is TACExpr.BinOp.SignExtend ||
                    it is TACExpr.BinRel.Gt ||
                    it is TACExpr.BinRel.Ge ||
                    it is TACExpr.BinRel.Lt ||
                    it is TACExpr.BinRel.Le ||
                    it is TACExpr.BinRel.Eq ||
                    it.cannotOverflow() != null
                }
            },
            repeat = 1,
            patternList = { listOf(
                /*
                    (x + c).mod() ~~> (x - abs(c)).mod()
                    where c is a 2's complement representation of a negative number
                */
                PatternHandler(
                    name = "add-flip-sign",
                    pattern = {
                        (lSym(A) + c(C1)).mod()
                    },
                    handle = {
                        maybeFlipSign(C1.n)?.let { (sym(A) sub it.asTACExpr).mod() }
                    },
                    TACExpr.BinOp.Mod::class.java
                ),

                /*
                    (x - c).mod() ~~> (x + (-c)).mod()
                    where c is a 2's complement representation of a negative number
                */
                PatternHandler(
                    name = "sub-flip-sign",
                    pattern = {
                        (lSym(A) - c(C1)).mod()
                    },
                    handle = {
                        maybeFlipSign(C1.n)?.let { (sym(A) add it.asTACExpr).mod() }
                    },
                    TACExpr.BinOp.Mod::class.java
                ),

                /*
                    (x + c).cannotOverflow().mod() ~~> (x - (-c)).cannotOverflow().mod()
                    where c is a 2's complement representation of a negative number

                    Note that "cannot overflow" here really applies to the *normalized* expression; it's not saying that
                    (x + c) cannot overflow, but rather that (x - (-c)) cannot overflow.  We have to allow this because
                    the compiler actually emits pointer math like `p + -8`, which literally overflows, but semantically
                    does not.
                */
                PatternHandler(
                    name = "add-flip-sign-no-ovf",
                    pattern = {
                        (lSym(A) + c(C1)).annotated(CANNOT_OVERFLOW_REASON).mod()
                    },
                    handle = {
                        maybeFlipSign(C1.n)?.let {
                            (sym(A) sub it.asTACExpr).annotated(CANNOT_OVERFLOW_REASON, "Flipped sign").mod()
                        }
                    },
                    TACExpr.BinOp.Mod::class.java
                ),

                /*
                    (-1 * x).mod() ~~> (x.mod() == 0) ? 0 : (modulus - x.mod())
                */
                PatternHandler(
                    name = "neg-mod",
                    pattern = {
                        (c((-1).to2s()) * lSym(A)).mod()
                    },
                    handle = {
                        ite(
                            sym(A).mod() eq 0.asTACExpr,
                            0.asTACExpr,
                            modulus.asTACExpr sub sym(A).mod()
                        )
                    },
                    TACExpr.BinOp.Mod::class.java
                ),
            ) }
        ).cleanup()
    }

    /**
        When generating TAC, we used information from the pointer analysis to annotate pointer math with
        [CANNOT_OVERFLOW_REASON], so that we can assert/assume those operations won't overflow.  Here we do an extra
        search for pointer math we might have missed, using a dataflow analysis to back-propagate pointer-ness inferred
        from uses as memory access locations.
     */
    private fun findMorePointers(code: CoreTACProgram): CoreTACProgram {
        val graph = code.analysisCache.graph
        val mbc = MustBeConstantAnalysis(graph)
        val def = code.analysisCache.def

        // Back-propagate the "pointer-ness" of all variables through the program.  If a variable is used as the
        // location of a memory access, it is a "pointer".  If a pointer is computed by adding a constant to another
        // variable, then the other variable is also a pointer.  Any other computation of a pointer is treated as
        // opaque.
        //
        // TODO CERT-10098: we should only mark operations that produce a pointer value, rather than marking all
        // operations that happen to have a pointer operand.
        val ptrAnalysis = object : TACCommandDataflowAnalysis<TreapSet<TACSymbol.Var>>(
            graph = graph,
            lattice = JoinLattice.ofJoin { a, b -> a union b },
            bottom = treapSetOf<TACSymbol.Var>(),
            dir = Direction.BACKWARD
        ) {
            override fun transformCmd(inState: TreapSet<TACSymbol.Var>, cmd: LTACCmd): TreapSet<TACSymbol.Var> {
                var outState = inState
                cmd.cmd.getLhs()?.let { outState -= it }
                outState += treapSetOfNotNull(
                    when (cmd.cmd) {
                        is TACCmd.Simple.DirectMemoryAccessCmd -> (cmd.cmd.loc as? TACSymbol.Var)
                        is TACCmd.Simple.AssigningCmd.AssignExpCmd -> runIf(cmd.cmd.lhs in inState) {
                            propagateTo(cmd.ptr, cmd.cmd.rhs) as? TACSymbol.Var
                        }
                        else -> null
                    }
                )
                return outState
            }

            // Given that [e] computes a location, find a variable in [e] which should also be considered a location.
            private fun propagateTo(where: CmdPointer, e: TACExpr): TACSymbol? = when (e) {
                is TACExpr.Sym -> mbc.mustBeConstantAt(where, e.s)?.let { TACSymbol.Const(it) } ?: e.s
                is TACExpr.AnnotationExp<*> -> propagateTo(where, e.o)
                is TACExpr.Vec.Add -> e.ls.map {
                    propagateTo(where, it) ?: return null
                }.singleOrNull {
                    it is TACSymbol.Var
                }
                is TACExpr.BinOp.Mod -> runIf(
                    e.o2 is TACExpr.Sym && mbc.mustBeConstantAt(where, e.o2.s) == modz64.modulus
                ) {
                    propagateTo(where, e.o1)
                }
                else -> null
            }

            init {
                runAnalysis()
            }
        }

        // Annotate expressions of the form: `ptr.mod(2^64)`, where `ptr` is not already annotated
        return code.parallelLtacStream().mapNotNull { (ptr, cmd) ->
            if (cmd !is TACCmd.Simple.AssigningCmd.AssignExpCmd) { return@mapNotNull null }
            if (cmd.rhs !is TACExpr.BinOp.Mod) { return@mapNotNull null }
            if (cmd.rhs.o2 !is TACExpr.Sym) { return@mapNotNull null }
            if (mbc.mustBeConstantAt(ptr, cmd.rhs.o2.s) != modz64.modulus) { return@mapNotNull null }
            val loc = cmd.rhs.o1 as? TACExpr.Sym.Var ?: return@mapNotNull null
            if (loc.s !in ptrAnalysis.cmdOut[ptr].orEmpty()) { return@mapNotNull null }

            // Check if this pointer value is already annotated
            val locDef = def.defSitesOf(loc.s, ptr).singleOrNull() ?: return@mapNotNull null
            val locDefCmd = graph.toCommand(locDef) as? TACCmd.Simple.AssigningCmd.AssignExpCmd ?: return@mapNotNull null
            if (locDefCmd.rhs is TACExpr.AnnotationExp<*>) { return@mapNotNull null }

            // `ptr.mod(2^64) ~~> ptr.cannotOverflow().mod(2^64)
            ptr to TXF {
                cmd.rhs.o1
                    .annotated(CANNOT_OVERFLOW_REASON, "inferred pointer")
                    .mod(cmd.rhs.o2)
            }.let { ExprUnfolder.unfoldTo(it, cmd.lhs, cmd.meta) }
        }.patchForEach(code) { (ptr, cmds) -> replaceCommand(ptr, cmds) }
    }

    /**
        For any expression annotated with [CANNOT_OVERFLOW_REASON], we add an assert/assume that the expression's result
        is indeed within bounds.  We also add asserts/assumes that any memory access locations are in the range of
        plausible memory addresses. Finally, we remove the mod operations on any expression annotated with
        [CANNOT_OVERFLOW_REASON], since they are redundant.
     */
    private fun removeNoOverflow(code: CoreTACProgram): CoreTACProgram {
        @Suppress("NAME_SHADOWING")
        var code = code

        // Add asserts/assumes for any annotated expressions
        code = code.parallelLtacStream().mapNotNull { (ptr, cmd) ->
            if (cmd !is TACCmd.Simple.AssigningCmd.AssignExpCmd) { return@mapNotNull null }
            val (reason, exp) = cmd.rhs.cannotOverflow() ?: return@mapNotNull null

            val cond = TXF { exp le modz64.maxUnsigned }
            val condVar = TACKeyword.TMP(Tag.Bool)
            val msg = "Cannot overflow: $reason"
            val meta = MetaMap(TACMeta.REMOVABLE_IF_TRIVIAL)

            ptr to listOf(
                TACCmd.Simple.AssigningCmd.AssignExpCmd(condVar, cond),
                if (optimistic) {
                    TACCmd.Simple.AssumeCmd(condVar, msg, meta)
                } else {
                    TACCmd.Simple.AssertCmd(condVar, msg, meta)
                }
            ).withDecls(condVar)
        }.patchForEach(code) { (ptr, cmds) -> addBefore(ptr, cmds) }

        // For each memory access, assume the address is within the range of plausible addresses.
        code = code.parallelLtacStream().mapNotNull { (ptr, cmd) ->
            if (cmd !is TACCmd.Simple.DirectMemoryAccessCmd) { return@mapNotNull null }
            val loc = cmd.loc as? TACSymbol.Var ?: return@mapNotNull null

            ptr to ExprUnfolder.unfoldPlusOneCmd(
                "boundedLoc",
                TXF { safeMathNarrowAssuming(loc.asSym(), Tag.Bit256, SBF_IMPLAUSIBLE_MEM_ADDRESS.toBigInteger()) },
                cmd.meta,
                { cmd.withLoc(it.s) }
            )
        }.patchForEach(code) { (ptr, cmds) -> replaceCommand(ptr, cmds) }

        // Remove the mod operations on any annotated expressions
        code = PatternRewriter.rewrite(
            code,
            repeat = 1,
            patternList = { listOf(
                /*
                    x.cannotOverflow().mod() ~~> x
                */
                PatternHandler(
                    name = "no-ovf",
                    pattern = {
                        lSym(A).annotated(CANNOT_OVERFLOW_REASON).mod()
                    },
                    handle = {
                        sym(A)
                    },
                    TACExpr.BinOp.Mod::class.java
                ),
            )}
        )

        return code.cleanup()
    }

    /**
        Simplifies expressions involving mod, using algebraic identities.  We apply these identities repeatedly (up
        to a configurable number of steps) to simplify complex expressions.

        This transform assumes the input code has already been normalized, and any [CANNOT_OVERFLOW_REASON] annotations
        have already been applied/eliminated.
     */
    private fun simplify(code: CoreTACProgram): CoreTACProgram {
        @Suppress("NAME_SHADOWING")
        var code = code
        code = PatternRewriter.rewrite(
            code,
            repeat = SolanaConfig.TACModSimplificationSteps.get(),
            patternList = { listOf(
                /*
                    (x + y).mod() < x ~~> (x.mod() + y.mod()) >= modulus
                */
                PatternHandler(
                    name = "add-ovf-1",
                    pattern = {
                        (lSym(A) + lSym(B)).mod() symmLt lSym(C)
                    },
                    handle = {
                        runIf(src(A) == src(C)) {
                            (sym(A).mod() intAdd sym(B).mod()) ge modulus.asTACExpr
                        }
                    },
                    TACExpr.BinRel.Gt::class.java, TACExpr.BinRel.Lt::class.java,
                ),

                /*
                    (x + y).mod() >= x ~~> (x.mod() + y.mod()) < modulus
                */
                PatternHandler(
                    name = "add-ovf-2",
                    pattern = {
                        (lSym(A) + lSym(B)).mod() symmGe lSym(C)
                    },
                    handle = {
                        runIf(src(A) == src(C)) {
                            (sym(A).mod() intAdd sym(B).mod()) lt modulus.asTACExpr
                        }
                    },
                    TACExpr.BinRel.Ge::class.java, TACExpr.BinRel.Le::class.java,
                ),

                /*
                    (x - y).mod() > x ~~> x.mod() < y.mod()
                */
                PatternHandler(
                    name = "sub-ovf-1",
                    pattern = {
                        (lSym(A) - lSym(B)).mod() symmGt lSym(C)
                    },
                    handle = {
                        runIf(src(A) == src(C)) {
                            sym(A).mod() lt sym(B).mod()
                        }
                    },
                    TACExpr.BinRel.Gt::class.java, TACExpr.BinRel.Lt::class.java,
                ),

                /*
                    (x - y).mod() <= x ~~> x.mod() >= y.mod()
                */
                PatternHandler(
                    name = "sub-ovf-2",
                    pattern = {
                        (lSym(A) - lSym(B)).mod() symmLe lSym(C)
                    },
                    handle = {
                        runIf(src(A) == src(C)) {
                            sym(A).mod() ge sym(B).mod()
                        }
                    },
                    TACExpr.BinRel.Ge::class.java, TACExpr.BinRel.Le::class.java,
                ),

                /*
                    ((x << n).mod().signExtend(64) >> n).mod() ~~> x.signExtend(64-n).mod()
                */
                PatternHandler(
                    name = "shl-mod-signext",
                    pattern = {
                        ((lSym(A) shl c(C1)).mod().signExtend() shra c(C2)).mod()
                    },
                    handle = {
                        runIf(C1.n == C2.n) {
                            val n = C1.n.toIntOrNull()?.takeIf { it in 0..<64 && it % 8 == 0 } ?: return@runIf null
                            SignExtend((((64 - n) / 8) - 1).asTACExpr, sym(A)).mod()
                        }
                    },
                    TACExpr.BinOp.Mod::class.java
                ),

                /*
                    x.signExtend(n).mod(2^64) <= (2^63-1) ~~> x.mod(2^n) <= (2^(n-1)-1)
                */
                PatternHandler(
                    name = "signext-mod-sign",
                    pattern = {
                        c(C1).signExtend(lSym(A)).mod() symmLe c(BigInteger.TWO.pow(63) - BigInteger.ONE)
                    },
                    handle = {
                        runIf(C1.n <= 7.toBigInteger()) {
                            val n = (C1.n.toInt() + 1) * 8
                            sym(A).mod(BigInteger.TWO.pow(n).asTACExpr) le
                                (BigInteger.TWO.pow(n - 1) - BigInteger.ONE).asTACExpr
                        }
                    },
                    TACExpr.BinRel.Ge::class.java, TACExpr.BinRel.Le::class.java
                ),

                /*
                    x.signExtend(n).mod(2^64) > 0 ~~> x.mod(2^n) > 0
                */
                PatternHandler(
                    name = "signext-mod-nonzero",
                    pattern = {
                        c(C1).signExtend(lSym(A)).mod() symmGt c(0)
                    },
                    handle = {
                        runIf(C1.n <= 7.toBigInteger()) {
                            val n = (C1.n.toInt() + 1) * 8
                            sym(A).mod(BigInteger.TWO.pow(n).asTACExpr) gt 0.asTACExpr
                        }
                    },
                    TACExpr.BinRel.Gt::class.java, TACExpr.BinRel.Lt::class.java
                ),

                /*
                    Signed > ~~> unsigned > :
                    x.signExtend() s> y.signExtend() ~~> (x.isNonNeg() && y.isNeg()) || (sameSign(x, y) && x > y)
                 */
                PatternHandler(
                    name = "gt-signed-to-unsigned",
                    pattern = {
                        lSym(A).signExtend() symmGt lSym(B).signExtend()
                    },
                    handle = {
                        // This transformation won't help in BV mode!
                        runIf(!bvMode) {
                            (sym(A).isNonNeg() and sym(B).isNeg()) or (sameSign(sym(A), sym(B)) and (sym(A) gt sym(B)))
                        }
                    },
                    TACExpr.BinRel.Gt::class.java, TACExpr.BinRel.Lt::class.java
                ),

                /*
                    Signed >= ~~> unsigned >= :
                    x.signExtend() s>= y.signExtend() ~~> (x.isNonNeg() && y.isNeg()) || (sameSign(x, y) && x >= y)
                 */
                PatternHandler(
                    name = "ge-signed-to-unsigned",
                    pattern = {
                        lSym(A).signExtend() symmGe lSym(B).signExtend()
                    },
                    handle = {
                        // This transformation won't help in BV mode!
                        runIf(!bvMode) {
                            (sym(A).isNonNeg() and sym(B).isNeg()) or (sameSign(sym(A), sym(B)) and (sym(A) ge sym(B)))
                        }
                    },
                    TACExpr.BinRel.Ge::class.java, TACExpr.BinRel.Le::class.java
                ),

                /*
                    x.mod() & maxUnsigned ~~> x & maxUnsigned
                */
                PatternHandler(
                    name = "mod-and",
                    pattern = {
                        lSym(A).mod() bwAnd c(modz64.maxUnsigned)
                    },
                    handle = {
                        sym(A) bwAnd modz64.maxUnsigned.asTACExpr
                    },
                    TACExpr.BinOp.BWAnd::class.java
                ),

                /*
                    x.mod().mod() ~~> x.mod()
                */
                PatternHandler(
                    name = "mod-mod",
                    pattern = {
                        lSym(A).mod().mod()
                    },
                    handle = {
                        sym(A).mod()
                    },
                    TACExpr.BinOp.Mod::class.java
                ),

                /*
                    (x.mod() + y).mod() ~~> (x + y).mod()
                    (x + y.mod()).mod() ~~> (x + y).mod()
                */
                PatternHandler(
                    name = "mod-add-simplify",
                    pattern = {
                        (lSym(A).mod() + lSym(B)).mod()
                    },
                    handle = {
                        (sym(A) add sym(B)).mod()
                    },
                    TACExpr.BinOp.Mod::class.java
                ),

                /*
                    (x.mod() - y).mod() ~~> (x - y).mod()
                */
                PatternHandler(
                    name = "mod-sub-simplify-1",
                    pattern = {
                        (lSym(A).mod() - lSym(B)).mod()
                    },
                    handle = {
                        (sym(A) sub sym(B)).mod()
                    },
                    TACExpr.BinOp.Mod::class.java
                ),

                /*
                    (x - y.mod()).mod() ~~> (x - y).mod()
                */
                PatternHandler(
                    name = "mod-sub-simplify-2",
                    pattern = {
                        (lSym(A) - lSym(B).mod()).mod()
                    },
                    handle = {
                        (sym(A) sub sym(B)).mod()
                    },
                    TACExpr.BinOp.Mod::class.java
                ),

                /*
                    (x.mod() * y).mod() ~~> (x * y).mod()
                    (x * y.mod()).mod() ~~> (x * y).mod()
                */
                PatternHandler(
                    name = "mod-mul-simplify",
                    pattern = {
                        (lSym(A).mod() * lSym(B)).mod()
                    },
                    handle = {
                        (sym(A) mul sym(B)).mod()
                    },
                    TACExpr.BinOp.Mod::class.java
                ),

                /*
                    (x.mod() - c).mod() == 0 ~~> x.mod() == c.mod()
                */
                PatternHandler(
                    name = "mod-sub-eq-simplify",
                    pattern = {
                        (lSym(A).mod() - c(C1)).mod() eq c(0)
                    },
                    handle = {
                        sym(A).mod() eq C1.n.mod(modulus).asTACExpr
                    },
                    TACExpr.BinRel.Eq::class.java
                ),
            ) }
        )

        // We only want to apply these patterns once, since they would otherwise expand recursively:
        code = PatternRewriter.rewrite(
            code,
            repeat = 1,
            patternList = { listOf(
                /*
                    x >> 63 ~~> (x >= 2^64) ? (x >> 63) : (x >= 2^63) ? 1 : 0

                    (This looks worse, but the interval rewriter will be able to eliminate the outer `ite` in most
                    cases)
                */
                PatternHandler(
                    name = "shr63-to-ite",
                    pattern = {
                        lSym(A) shr c(63)
                    },
                    handle = {
                        ite(
                            sym(A) ge modulus.asTACExpr,
                            sym(A) shiftRLog 63.asTACExpr,
                            ite(
                                sym(A) ge (modulus / 2).asTACExpr,
                                1.asTACExpr,
                                0.asTACExpr
                            )
                        )
                    },
                    TACExpr.BinOp.ShiftRightLogical::class.java
                ),
            ) }
        )
        return code.cleanup()
    }
}
