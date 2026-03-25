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

import sbf.cfg.*
import sbf.disassembler.SbfRegister
import vc.data.*
import java.math.BigInteger
import datastructures.stdcollections.*
import sbf.SolanaConfig
import sbf.callgraph.CVTU128Intrinsics
import sbf.domains.INumValue
import sbf.domains.IOffset
import sbf.domains.IPTANodeFlags
import sbf.sbfLogger

/**
 * Dispatches TAC summarization for an u128 intrinsic call.
 *
 * The calls handled here are not present in the original Solana bytecode.
 * They are introduced in one of two ways:
 *  - By a front-end CFG transformation (e.g. [promoteMathIntrinsics]) that recognizes
 *    sequences of low-level SBF instructions implementing a 128-bit operation and
 *    replaces them with a single call to the corresponding intrinsic.
 *  - By cvlr, which emits calls to these intrinsics directly when compiling
 *    specification expressions that operate on u128 values.
 **/
context(SbfCFGToTAC<TNum, TOffset, TFlags>)
internal fun <TNum : INumValue<TNum>, TOffset : IOffset<TOffset>, TFlags: IPTANodeFlags<TFlags>> summarizeU128(
    locInst: LocatedSbfInstruction
): List<TACCmd.Simple> {
    val inst = locInst.inst
    check(inst is SbfInstruction.Call) {"summarizeU128 expects a call instruction instead of ${locInst.inst}"}
    val function = CVTU128Intrinsics.from(inst.name)
    check(function != null) {"summarizeU128 does not support ${inst.name}"}
    return when (function) {
        CVTU128Intrinsics.U128_LEQ -> summarizeU128Leq(locInst)
        CVTU128Intrinsics.U128_GT0 -> summarizeU128Gt0(locInst)
        CVTU128Intrinsics.U128_CEIL_DIV -> summarizeU128CeilDiv(locInst)
        CVTU128Intrinsics.U128_NONDET -> summarizeU128Nondet(locInst)
        CVTU128Intrinsics.U128_WRAPPING_SUBTRACTION -> summarizeU128WrappingSubtraction(locInst)
    }
}

/**
 * Given `r1: low(x)`, `r2: high(x)`, `r3: low(y)`, `r4: high(y)` and `result` in `r0`
 *
 * We do case by case using nested ite terms
 * 1. if `high(x) == 0` and `high(y) == 0` then `low(x) <= low(y)`
 * 2. if `high(x) == 0` and `high(y) != 0` then `true`
 * 3. if `high(x) != 0` and `high(y) == 0` then `false`
 * 4. if `high(x) != 0` and `high(y) != 0` then `(high(x) << 64 + low(x)) <= (high(y) << 64 + low(y))`
 **/
context(SbfCFGToTAC<TNum, TOffset, TFlags>)
internal fun <TNum : INumValue<TNum>, TOffset : IOffset<TOffset>, TFlags: IPTANodeFlags<TFlags>> summarizeU128Leq(
    locInst: LocatedSbfInstruction
): List<TACCmd.Simple> {
    val inst = locInst.inst
    check(inst is SbfInstruction.Call)
    {"summarizeU128Leq expects a call instruction instead of ${locInst.inst}"}
    check(CVTU128Intrinsics.from(inst.name) == CVTU128Intrinsics.U128_LEQ)
    {"summarizeU128Leq expects ${CVTU128Intrinsics.U128_LEQ.function.name}"}

    val res = exprBuilder.mkVar(SbfRegister.R0)
    val xLowE = exprBuilder.mkExprSym(Value.Reg(SbfRegister.R1))
    val xHighE = exprBuilder.mkExprSym(Value.Reg(SbfRegister.R2))
    val yLowE = exprBuilder.mkExprSym(Value.Reg(SbfRegister.R3))
    val yHighE = exprBuilder.mkExprSym(Value.Reg(SbfRegister.R4))

    val cmds = mutableListOf<TACCmd.Simple>()
    cmds += Debug.startFunction(inst.name)
    val xE = mergeU128(xLowE, xHighE, cmds)
    val yE = mergeU128(yLowE, yHighE, cmds)
    val cond = TACExpr.TernaryExp.Ite(
        TACExpr.BinBoolOp.LAnd(
            TACExpr.BinRel.Eq(xHighE, TACExpr.zeroExpr),
            TACExpr.BinRel.Eq(yHighE, TACExpr.zeroExpr)),
        exprBuilder.mkBinRelExp(CondOp.LE, xLowE, yLowE),
        TACExpr.TernaryExp.Ite(
            TACExpr.BinBoolOp.LAnd(
                TACExpr.BinRel.Eq(xHighE, TACExpr.zeroExpr),
                TACExpr.UnaryExp.LNot(TACExpr.BinRel.Eq(yHighE, TACExpr.zeroExpr))),
            TACSymbol.True.asSym(),
            TACExpr.TernaryExp.Ite(
                TACExpr.BinBoolOp.LAnd(
                    TACExpr.UnaryExp.LNot(TACExpr.BinRel.Eq(xHighE, TACExpr.zeroExpr)),
                    TACExpr.BinRel.Eq(yHighE, TACExpr.zeroExpr)),
                TACSymbol.False.asSym(),
                exprBuilder.mkBinRelExp(CondOp.LE, xE.asSym(), yE.asSym()),
            )
        )
    )
    cmds += assign(res, TACExpr.TernaryExp.Ite(cond, exprBuilder.ONE.asSym(), TACExpr.zeroExpr))
    cmds += Debug.endFunction(inst.name)
    return cmds
}

/**
 *  Given `r1: low(x)`, `r2: high(x)` and `res` in `r0` compute:
 *  ```
 *  high(x) != 0 || low(x) > 0
 *  ```
 */
context(SbfCFGToTAC<TNum, TOffset, TFlags>)
internal fun <TNum : INumValue<TNum>, TOffset : IOffset<TOffset>, TFlags: IPTANodeFlags<TFlags>> summarizeU128Gt0(
    locInst: LocatedSbfInstruction
): List<TACCmd.Simple> {
    val inst = locInst.inst
    check(inst is SbfInstruction.Call)
    { "summarizeU128Gt0 expects a call instruction instead of ${locInst.inst}" }
    check(CVTU128Intrinsics.from(inst.name) == CVTU128Intrinsics.U128_GT0)
    { "summarizeU128Gt0 expects ${CVTU128Intrinsics.U128_GT0.function.name}" }

    val res = exprBuilder.mkVar(SbfRegister.R0)
    val xLowE  = exprBuilder.mkExprSym(Value.Reg(SbfRegister.R1))
    val xHighE = exprBuilder.mkExprSym(Value.Reg(SbfRegister.R2))

    val cmds = mutableListOf<TACCmd.Simple>()
    cmds += Debug.startFunction(inst.name)
    cmds += assign(res, TACExpr.BinBoolOp.LOr(
        TACExpr.UnaryExp.LNot(TACExpr.BinRel.Eq(xHighE, TACExpr.zeroExpr)),
        exprBuilder.mkBinRelExp(CondOp.GT, xLowE, TACExpr.zeroExpr))
    )
    cmds += Debug.endFunction(inst.name)
    return cmds
}

/**
 * Given `r2: low(x)`, `r3: high(x)`, `r4: low(y)`, `r5: high(y)`, `low(result)` in `*(r0+0)`, and `high(result)` in `*(r0+8)`
 * compute:
 * ```
 * ceil_div(x, y) = (x + y - 1) / y
 * ```
 * where `x = high(x) << 64 + low(x)` and `y = high(y) << 64 + low(y)`
 */
context(SbfCFGToTAC<TNum, TOffset, TFlags>)
internal fun <TNum : INumValue<TNum>, TOffset : IOffset<TOffset>, TFlags: IPTANodeFlags<TFlags>> summarizeU128CeilDiv(
    locInst: LocatedSbfInstruction
): List<TACCmd.Simple> {
    val inst = locInst.inst
    check(inst is SbfInstruction.Call)
    { "summarizeU128CeilDiv expects a call instruction instead of ${locInst.inst}" }
    check(CVTU128Intrinsics.from(inst.name) == CVTU128Intrinsics.U128_CEIL_DIV)
    { "summarizeU128CeilDiv expects ${CVTU128Intrinsics.U128_CEIL_DIV.function.name}" }

    if (!SolanaConfig.UseTACMathInt.get()) {
        sbfLogger.warn {"${locInst.inst} will not be modeled precisely in TAC. " +
            "Enable ${SolanaConfig.UseTACMathInt.name} for a precise modeling" }
        return summarizeCall(locInst)
    }

    val (resLow, resHigh, overflow) = getResFrom128(locInst) ?: return listOf()
    val xLowE  = exprBuilder.mkVar(SbfRegister.R2).asSym()
    val xHighE = exprBuilder.mkVar(SbfRegister.R3).asSym()
    val yLowE  = exprBuilder.mkVar(SbfRegister.R4).asSym()
    val yHighE = exprBuilder.mkVar(SbfRegister.R5).asSym()
    val args = U128BinaryOperands(resLow.tacVar, resHigh.tacVar, overflow?.tacVar, xLowE, xHighE, yLowE, yHighE)

    val xMath = vFac.mkFreshMathIntVar()
    val yMath = vFac.mkFreshMathIntVar()
    val resMath = vFac.mkFreshMathIntVar()

    val cmds = mutableListOf<TACCmd.Simple>()
    cmds += Debug.startFunction(inst.name)
    applyU128BinaryOperation(args, cmds) { res, _, x, y ->
        cmds += promoteToMathInt(x.asSym(), xMath)
        cmds += promoteToMathInt(y.asSym(), yMath)
        cmds += assign(resMath, TACExpr.BinOp.IntDiv(
            TACExpr.BinOp.IntSub(TACExpr.Vec.IntAdd(xMath.asSym(), yMath.asSym()), exprBuilder.ONE.asSym()),
            yMath.asSym())
        )
        cmds += narrowFromMathInt(resMath.asSym(), res)
    }
    cmds += Debug.endFunction(inst.name)
    return cmds
}

/**
 * Given `low(result)` in `*(r0+0)`, and  `high(result)` in `*(r0+8)` compute
 *
 * ```
 * result < 2^128
 * ```
 * where `result = high(result) << 64 + low(result)`
 **/
context(SbfCFGToTAC<TNum, TOffset, TFlags>)
internal fun <TNum : INumValue<TNum>, TOffset : IOffset<TOffset>, TFlags: IPTANodeFlags<TFlags>> summarizeU128Nondet(
    locInst: LocatedSbfInstruction
): List<TACCmd.Simple> {
    val inst = locInst.inst
    check(inst is SbfInstruction.Call)
    { "summarizeU128Nondet expects a call instruction instead of ${locInst.inst}" }
    check(CVTU128Intrinsics.from(inst.name) == CVTU128Intrinsics.U128_NONDET)
    { "summarizeU128Nondet expects ${CVTU128Intrinsics.U128_NONDET.function.name}" }

    val (resLow, resHigh) = getResFrom128(locInst) ?: return listOf()
    val res = vFac.mkFreshIntVar()

    val cmds = mutableListOf<TACCmd.Simple>()
    cmds += Debug.startFunction(inst.name)
    cmds += inRange(res, BigInteger.ZERO,  BigInteger.TWO.pow(128))
    cmds += splitU128(res, resLow.tacVar, resHigh.tacVar)
    cmds += Debug.endFunction(inst.name)
    return cmds
}


/**
 * Summarizes an u128 wrapping subtraction intrinsic.
 *
 * Computes `result = (x - y) mod 2^128`, where:
 *  - `x` is the 128-bit value whose low half is in R1 and high half is in R2.
 *  - `y` is the 128-bit value whose low half is in R3 and high half is in R4.
 *
 * The result is written to two map locations provided by the memory summary:
 *  1. `*(summary[0])` — low half of the result.
 *  2. `*(summary[1])` — high half of the result.
 *
 * There is no overflow flag: wrapping subtraction always produces a valid u128.
 *
 * Unlike other external functions, when `u128_wrapping_subtraction` returns `r0` points to a heap allocated memory of 16 bytes
 * where `*(u64*)r0` contains `resLow` and `*(u64*)r0+8` contains resHigh.
 */
context(SbfCFGToTAC<TNum, TOffset, TFlags>)
internal fun <TNum : INumValue<TNum>, TOffset : IOffset<TOffset>, TFlags: IPTANodeFlags<TFlags>> summarizeU128WrappingSubtraction(
    locInst: LocatedSbfInstruction
): List<TACCmd.Simple> {
    val inst = locInst.inst
    check(inst is SbfInstruction.Call)
    { "summarizeU128WrappingSubtraction expects a call instruction instead of ${locInst.inst}" }
    check(CVTU128Intrinsics.from(inst.name) == CVTU128Intrinsics.U128_WRAPPING_SUBTRACTION)
    { "summarizeU128WrappingSubtraction expects ${CVTU128Intrinsics.U128_WRAPPING_SUBTRACTION.function.name}" }

    val summaryArgs = mem.getTACMemoryFromSummary(locInst) ?: return listOf()
    if (summaryArgs.size != 2) {
        return listOf()
    }

    val resLowMap  = summaryArgs[0].variable as? TACByteMapVariable ?: return listOf()
    val resHighMap = summaryArgs[1].variable as? TACByteMapVariable ?: return listOf()

    val resLow  = vFac.mkFreshIntVar()
    val resHigh = vFac.mkFreshIntVar()
    val xLowE   = exprBuilder.mkVar(SbfRegister.R1).asSym()
    val xHighE  = exprBuilder.mkVar(SbfRegister.R2).asSym()
    val yLowE   = exprBuilder.mkVar(SbfRegister.R3).asSym()
    val yHighE  = exprBuilder.mkVar(SbfRegister.R4).asSym()
    val args = U128BinaryOperands(resLow, resHigh, null, xLowE, xHighE, yLowE, yHighE)

    val cmds = mutableListOf<TACCmd.Simple>()

    cmds += Debug.startFunction(name= inst.name)
    // We assign a symbolic address to the returned pointer.
    check(summaryArgs[0].reg == summaryArgs[1].reg)
    val ptrV = exprBuilder.mkVar(summaryArgs[0].reg)
    val allocatedSpace = 16UL
    cmds += heapMemAlloc.alloc(ptrV, allocatedSpace)

    // The TAC code for wrapping subtraction
    // 1. Merge low and high halves
    // 2. SUB in bv256
    // 3. mask with 2^128 -1
    // 4. split into two halves again
    // Steps 1, 3, and 4 are done as part of `applyU128BinaryOperation`
    applyU128BinaryOperation(args, cmds) { res, _, x, y ->
        cmds += assign(res, exprBuilder.mkSubExpr(x.asSym(), y.asSym(), false))
    }

    // Store resLow in `*(u64*)r0` and highLow in `*(u64*)r0+8`.
    // Since r0 is a heap pointer their contents are modeled by TAC ByteMap's.
    cmds += mapStores(resLowMap,  ptrV, summaryArgs[0].offset, resLow)
    cmds += mapStores(resHighMap, ptrV, summaryArgs[1].offset, resHigh)
    cmds += Debug.endFunction(name = inst.name)
    return cmds
}
