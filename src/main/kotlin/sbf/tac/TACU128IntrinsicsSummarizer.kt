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
import java.math.BigInteger
import datastructures.stdcollections.*
import sbf.SolanaConfig
import sbf.callgraph.CVTU128Intrinsics
import sbf.domains.INumValue
import sbf.domains.IOffset
import sbf.domains.IPTANodeFlags
import sbf.sbfLogger
import vc.data.TACCmd
import vc.data.TACExpr
import vc.data.TACSymbol

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
        CVTU128Intrinsics.U128_WRAPPING_ADDITION -> summarizeU128WrappingAddition(locInst)
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

    val res    = sbfTacB.mkVar(SbfRegister.R0)
    val xLowE  = sbfTacB.mkExprSym(Value.Reg(SbfRegister.R1))
    val xHighE = sbfTacB.mkExprSym(Value.Reg(SbfRegister.R2))
    val yLowE  = sbfTacB.mkExprSym(Value.Reg(SbfRegister.R3))
    val yHighE = sbfTacB.mkExprSym(Value.Reg(SbfRegister.R4))

    val cmds = mutableListOf<TACCmd.Simple>()
    cmds += Debug.startFunction(inst.name)
    applyU128RelationalOperation(res, xLowE, xHighE, yLowE, yHighE, cmds) { x, y ->
        sbfTacB { ite(x le y, ONE, ZERO) }
    }
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

    val res    = sbfTacB.mkVar(SbfRegister.R0)
    val xLowE  = sbfTacB.mkExprSym(Value.Reg(SbfRegister.R1))
    val xHighE = sbfTacB.mkExprSym(Value.Reg(SbfRegister.R2))
    val cmds = mutableListOf<TACCmd.Simple>()
    cmds += Debug.startFunction(inst.name)
    applyU128RelationalOperation(res, xLowE, xHighE, cmds) { x ->
        sbfTacB { ite(x gt ZERO, ONE, ZERO) }
    }
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
    val xLowE  = sbfTacB.mkVar(SbfRegister.R2).asSym()
    val xHighE = sbfTacB.mkVar(SbfRegister.R3).asSym()
    val yLowE  = sbfTacB.mkVar(SbfRegister.R4).asSym()
    val yHighE = sbfTacB.mkVar(SbfRegister.R5).asSym()
    val args = U128BinaryOperands(resLow.tacVar, resHigh.tacVar, overflow?.tacVar, xLowE, xHighE, yLowE, yHighE)

    val xMath   = vFac.mkFreshMathIntVar()
    val yMath   = vFac.mkFreshMathIntVar()
    val resMath = vFac.mkFreshMathIntVar()

    val cmds = mutableListOf<TACCmd.Simple>()
    cmds += Debug.startFunction(inst.name)
    applyU128BinaryOperation(args, cmds) { res, _, x, y ->
        cmds += promoteToMathInt(x.asSym(), xMath)
        cmds += promoteToMathInt(y.asSym(), yMath)
        cmds += assign(resMath, sbfTacB { ((xMath intAdd yMath) intSub ONE) intDiv yMath })
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
    cmds += splitU128(res.asSym(), resLow.tacVar, resHigh.tacVar)
    cmds += Debug.endFunction(inst.name)
    return cmds
}


/**
 * Shared implementation for u128 wrapping binary operations (addition, subtraction).
 *
 * Computes `result = op(x, y) mod 2^128`, where:
 *  - `x` is the 128-bit value whose low half is in R1 and high half is in R2.
 *  - `y` is the 128-bit value whose low half is in R3 and high half is in R4.
 *
 * [op] performs the actual 256-bit operation on the merged operands and is provided
 * by the caller.
 *
 * The result is written to heap memory pointed to by r0:
 *  `*(u64*)r0` contains `resLow` and `*(u64*)r0+8` contains `resHigh`.
 */
context(SbfCFGToTAC<TNum, TOffset, TFlags>)
private fun <TNum : INumValue<TNum>, TOffset : IOffset<TOffset>, TFlags: IPTANodeFlags<TFlags>> summarizeU128WrappingBinaryOp(
    locInst: LocatedSbfInstruction,
    expected: CVTU128Intrinsics,
    op: (TACSymbol.Var, TACSymbol.Var) -> TACExpr
): List<TACCmd.Simple> {
    val inst = locInst.inst
    check(inst is SbfInstruction.Call)
    { "${expected.function.name} expects a call instruction instead of ${locInst.inst}" }
    check(CVTU128Intrinsics.from(inst.name) == expected)
    { "Expected ${expected.function.name} but got ${inst.name}" }

    val summaryArgs = mem.getTACMemoryFromSummary(locInst) ?: return listOf()
    if (summaryArgs.size != 2) {
        return listOf()
    }

    val resLowMap  = summaryArgs[0].variable as? TACByteMapVariable ?: return listOf()
    val resHighMap = summaryArgs[1].variable as? TACByteMapVariable ?: return listOf()

    val resLow  = vFac.mkFreshIntVar()
    val resHigh = vFac.mkFreshIntVar()
    val xLowE   = sbfTacB.mkVar(SbfRegister.R1).asSym()
    val xHighE  = sbfTacB.mkVar(SbfRegister.R2).asSym()
    val yLowE   = sbfTacB.mkVar(SbfRegister.R3).asSym()
    val yHighE  = sbfTacB.mkVar(SbfRegister.R4).asSym()
    val args = U128BinaryOperands(resLow, resHigh, null, xLowE, xHighE, yLowE, yHighE)

    val cmds = mutableListOf<TACCmd.Simple>()

    cmds += Debug.startFunction(name = inst.name)
    // We assign a symbolic address to the returned pointer.
    check(summaryArgs[0].reg == summaryArgs[1].reg)
    val ptrV = sbfTacB.mkVar(summaryArgs[0].reg)
    cmds += heapMemAlloc.alloc(ptrV, 16UL)

    // 1. Merge low and high halves
    // 2. Apply op in bv256
    // 3. mask with 2^128 - 1
    // 4. split into two halves again
    // Steps 1, 3, and 4 are done as part of `applyU128BinaryOperation`
    applyU128BinaryOperation(args, cmds) { res, _, x, y ->
        cmds += assign(res, op(x, y))
    }

    // Store resLow in `*(u64*)r0` and resHigh in `*(u64*)r0+8`.
    // Since r0 is a heap pointer their contents are modeled by TAC ByteMap's.
    cmds += mapStores(resLowMap,  ptrV, summaryArgs[0].offset, resLow)
    cmds += mapStores(resHighMap, ptrV, summaryArgs[1].offset, resHigh)
    cmds += Debug.endFunction(name = inst.name)
    return cmds
}

context(SbfCFGToTAC<TNum, TOffset, TFlags>)
internal fun <TNum : INumValue<TNum>, TOffset : IOffset<TOffset>, TFlags: IPTANodeFlags<TFlags>> summarizeU128WrappingSubtraction(
    locInst: LocatedSbfInstruction
): List<TACCmd.Simple> =
    summarizeU128WrappingBinaryOp(locInst, CVTU128Intrinsics.U128_WRAPPING_SUBTRACTION) { x, y -> sbfTacB { x sub y } }

context(SbfCFGToTAC<TNum, TOffset, TFlags>)
internal fun <TNum : INumValue<TNum>, TOffset : IOffset<TOffset>, TFlags: IPTANodeFlags<TFlags>> summarizeU128WrappingAddition(
    locInst: LocatedSbfInstruction
): List<TACCmd.Simple> =
    summarizeU128WrappingBinaryOp(locInst, CVTU128Intrinsics.U128_WRAPPING_ADDITION) { x, y -> sbfTacB { x add y } }
