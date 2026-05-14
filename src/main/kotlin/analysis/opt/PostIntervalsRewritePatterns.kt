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

package analysis.opt

import analysis.LTACSymbol
import analysis.opt.PatternRewriter.Key.*
import analysis.opt.intervals.IntervalsRewriter.Companion.NON_ZERO_META
import analysis.patterns.Info
import analysis.patterns.get
import config.Config
import utils.*
import vc.data.TACExpr
import vc.data.TACSymbol
import vc.data.asTACExpr
import java.math.BigInteger


private fun Info.isNonZero(key: PatternRewriter.Key<LTACSymbol>): Boolean =
    when (val sym = this[key]!!.symbol) {
        is TACSymbol.Const -> sym.value != BigInteger.ZERO
        is TACSymbol.Var -> sym.meta.contains(NON_ZERO_META)
    }


/**
 * Patterns that should run after [analysis.opt.intervals.IntervalsRewriter] so that they can rely on the
 * non-zero-ness information it propagates via [NON_ZERO_META].
 *
 * Note that the 5 div rewrite patterns rely on [Config.Smt.UseBV] being false, because if we use a 256 bit
 * bitvector representation, the multiplication may overflow, making these patterns wrong.
 */
fun PatternRewriter.postIntervalsRewriterPatternList() = listOfNotNull(

    /**
     * `A / B < C`  ~~>  `A < B·C`     (when B != 0)
     * Multiplication is in the integer domain so it can't overflow.
     */
    patternOnlyIf(
        cond = !Config.Smt.UseBV.get(),
        name = "divLt",
        pattern = {
            (lSym256(A) / lSym256(B)) lt lSym256(C)
        },
        handle = {
            runIf(info.isNonZero(B)) {
                Lt(sym(A), IntMul(sym(B), sym(C)))
            }
        },
        TACExpr.BinRel.Lt::class.java
    ),

    /**
     * `A / B <= C`  ~~>  `A < B·(C+1)`     (when B != 0)
     */
    patternOnlyIf(
        cond = !Config.Smt.UseBV.get(),
        name = "divLe",
        pattern = {
            (lSym256(A) / lSym256(B)) le lSym256(C)
        },
        handle = {
            runIf(info.isNonZero(B)) {
                Lt(sym(A), IntMul(sym(B), IntAdd(sym(C), 1.asTACExpr)))
            }
        },
        TACExpr.BinRel.Le::class.java
    ),

    /**
     * `A / B > C`  ~~>  `A >= B·(C+1)`     (when B != 0)
     */
    patternOnlyIf(
        cond = !Config.Smt.UseBV.get(),
        name = "divGt",
        pattern = {
            (lSym256(A) / lSym256(B)) gt lSym256(C)
        },
        handle = {
            runIf(info.isNonZero(B)) {
                Ge(sym(A), IntMul(sym(B), IntAdd(sym(C), 1.asTACExpr)))
            }
        },
        TACExpr.BinRel.Gt::class.java
    ),

    /**
     * `A / B >= C`  ~~>  `A >= B·C`     (when B != 0)
     */
    patternOnlyIf(
        cond = !Config.Smt.UseBV.get(),
        name = "divGe",
        pattern = {
            (lSym256(A) / lSym256(B)) ge lSym256(C)
        },
        handle = {
            runIf(info.isNonZero(B)) {
                Ge(sym(A), IntMul(sym(B), sym(C)))
            }
        },
        TACExpr.BinRel.Ge::class.java
    ),

    /**
     * `A / B == C`  ~~>  `B·C <= A < B·(C+1)`     (when B != 0)
     */
    patternOnlyIf(
        cond = !Config.Smt.UseBV.get(),
        name = "divEq",
        pattern = {
            (lSym256(A) / lSym256(B)) eq lSym256(C)
        },
        handle = {
            runIf(info.isNonZero(B)) {
                LAnd(
                    Ge(sym(A), IntMul(sym(B), sym(C))),
                    Lt(sym(A), IntMul(sym(B), IntAdd(sym(C), 1.asTACExpr)))
                )
            }
        },
        TACExpr.BinRel.Eq::class.java
    ),

)
