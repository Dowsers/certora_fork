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

import datastructures.stdcollections.*
import sbf.domains.*
import utils.*
import vc.data.TACCmd
import vc.data.TACExpr
import vc.data.TACSymbol

/**
 * Summarize floating point operations assuming IEEE-754 double precision (f64).
 *
 *  ```
 *      1       11          52
 *  | sign | exponent | mantissa |
 *  ```
 *
 * Not all functions are currently summarized. The current summaries just look at the bit patterns.
 **/
open class SummarizeFPCompilerRt<TNum : INumValue<TNum>, TOffset : IOffset<TOffset>, TFlags: IPTANodeFlags<TFlags>> {

    private val plusInfBits = 0x7FF0_0000_0000_0000UL.toBigInteger()
    private val minusInfBits = 0xFFF0_0000_0000_0000UL.toBigInteger()
    private val minusZeroBits = 0x8000_0000_0000_0000UL.toBigInteger()
    private val minPositiveBits = 0x0010_0000_0000_0000UL.toBigInteger()
    private val twoBits = 0x4000_0000_0000_0000UL.toBigInteger()

    /**
     * Build expression for [v] to be `NaN`.
     *
     * Any number with all ones for exponent bits and non-zero mantissa bits is a NaN.
     * ```
     *    let exponent = bits & 0x7FF0000000000000;
     *    let mantissa = bits & 0x000FFFFFFFFFFFFF;
     *    exponent == 0x7FF0000000000000 && mantissa != 0
     * ```
     * In a numerical way, without bitwise operations, any bit pattern greater than `+oo` is a NaN.
     **/
    context(SbfCFGToTAC<TNum, TOffset, TFlags>)
    private fun isf64NaN(v: TACSymbol): TACExpr {
        val plusInf = sbfTacB.mkConst(plusInfBits).asSym()
        val v64 = sbfTacB.mask64(v.asSym())
        return sbfTacB { v64 gt plusInf}
    }

    context(SbfCFGToTAC<TNum, TOffset, TFlags>)
    private fun isNotf64NaN(v: TACSymbol) = sbfTacB { not(isf64NaN(v)) }

    /** Build expression for [v] to be `+oo` or `-oo` **/
    context(SbfCFGToTAC<TNum, TOffset, TFlags>)
    private fun isf64Inf(v: TACSymbol): TACExpr {
        val plusInf = sbfTacB.mkConst(plusInfBits).asSym()
        val minusInf = sbfTacB.mkConst(minusInfBits).asSym()
        val v64 = sbfTacB.mask64(v.asSym())
        return sbfTacB { (v64 eq plusInf) or (v64 eq minusInf)}
    }

    context(SbfCFGToTAC<TNum, TOffset, TFlags>)
    private fun isNotf64Inf(v: TACSymbol) = sbfTacB { not(isf64Inf(v)) }

    /** Build expression for [v] to be `+0` **/
    context(SbfCFGToTAC<TNum, TOffset, TFlags>)
    private fun isf64PlusZero(v: TACSymbol): TACExpr {
        val v64 = sbfTacB.mask64(v.asSym())
        return sbfTacB { (v64 eq sbfTacB.ZERO)}
    }

    /** Build expression for [v] to be `-0` **/
    context(SbfCFGToTAC<TNum, TOffset, TFlags>)
    private fun isf64MinusZero(v: TACSymbol): TACExpr {
        val v64 = sbfTacB.mask64(v.asSym())
        return sbfTacB { v64 eq sbfTacB.mkConst(minusZeroBits).asSym() }
    }

    /** Build expression for [v] to be `+0` or `-0` **/
    context(SbfCFGToTAC<TNum, TOffset, TFlags>)
    private fun isf64Zero(v: TACSymbol) = sbfTacB { isf64PlusZero(v) or isf64MinusZero(v) }

    context(SbfCFGToTAC<TNum, TOffset, TFlags>)
    private fun isf64NonZero(v: TACSymbol) = sbfTacB { not(isf64Zero(v)) }

    /** Build expression for [v] to be any positive number, included infinite, zero and subnormal numbers **/
    context(SbfCFGToTAC<TNum, TOffset, TFlags>)
    private fun isf64Positive(v: TACSymbol): TACExpr {
        // v >> 63 == 0
        return sbfTacB { (v.asSym() shiftRLog  mkConst(63).asSym())  eq sbfTacB.ZERO }
    }

    context(SbfCFGToTAC<TNum, TOffset, TFlags>)
    private fun isf64Negative(v: TACSymbol) = sbfTacB { not(isf64Positive(v)) }

    // REVISIT: the bitwise-and to clear MSB might be too complex for prover's axioms
    context(SbfCFGToTAC<TNum, TOffset, TFlags>)
    private fun isf64Subnormal(v: TACSymbol): TACExpr {
        // clear MSB
        val posNum = sbfTacB { v.asSym() bwAnd sbfTacB.mkConst(0x7FFF_FFFF_FFFF_FFFFUL.toBigInteger()) }
        return  sbfTacB { posNum gt sbfTacB.ZERO and (posNum lt sbfTacB.mkConst(minPositiveBits).asSym()) }
    }

    context(SbfCFGToTAC<TNum, TOffset, TFlags>)
    private fun isf64NonSubnormal(v: TACSymbol) = sbfTacB {  not(isf64Subnormal(v)) }

    /**
     * Build expression for [v] to be finite number, included subnormal numbers.
     *
     * Any finite number, including subnormal numbers, must have exponent different from  `0x7FF`
     **/
    context(SbfCFGToTAC<TNum, TOffset, TFlags>)
    private fun isFinite(v: TACSymbol): TACExpr {
        val plusInf = sbfTacB.mkConst(plusInfBits).asSym()
        return sbfTacB { v.asSym() lt plusInf}
    }

    /** Build expression if [v] is equal to 2 as f64 **/
    context(SbfCFGToTAC<TNum, TOffset, TFlags>)
    internal fun isTwo(v: TACSymbol): TACExpr {
        val two = sbfTacB.mkConst(twoBits).asSym()
        return sbfTacB { v.asSym() eq two }
    }

    /**
     * ```
     * int __unorddf2(double arg1, double arg2) {
     *    return (isnan(arg1) || isnan(arg2)) ? 1 : 0;
     * }
     * ```
     */
     context(SbfCFGToTAC<TNum, TOffset, TFlags>)
     internal fun summarizeUnorddf2(
        res: TACSymbol.Var,
        arg1: TACSymbol,
        arg2: TACSymbol
    ): List<TACCmd.Simple> =
        listOf(
            assign(res,
                sbfTacB{
                    switch(
                        isf64NaN(arg1) or isf64NaN(arg2)  to ONE,
                        default = ZERO
                    )
                }
            )

        )

    context(SbfCFGToTAC<TNum, TOffset, TFlags>)
    internal fun summarizeAdddf3(
        res: TACSymbol.Var,
        @Suppress("UNUSED_PARAMETER")
        arg1: TACSymbol,
        @Suppress("UNUSED_PARAMETER")
        arg2: TACSymbol
    ): List<TACCmd.Simple> = listOf(havoc(res))


    context(SbfCFGToTAC<TNum, TOffset, TFlags>)
    internal fun summarizeSubdf3(
        res: TACSymbol.Var,
        @Suppress("UNUSED_PARAMETER")
        arg1: TACSymbol,
        @Suppress("UNUSED_PARAMETER")
        arg2: TACSymbol
    ): List<TACCmd.Simple> = listOf(havoc(res))

    /**
     * ```
     * if isNaN(arg1) || isNaN(arg2) {
     *    NaN
     * } else if (isInf(arg1) && arg2 ==0 ) || (arg1 == 0 && isInf(arg2) {
     *    NaN
     * } else if (isInf(arg1) || isInf(arg2)) {
     *    Inf
     * } else if (arg1 == 0 || arg2 == 0) {
     *    0
     * } else {
     *    nondet
     * }
     * ```
     */
    context(SbfCFGToTAC<TNum, TOffset, TFlags>)
    internal fun summarizeMuldf3(
        res: TACSymbol.Var,
        arg1: TACSymbol,
        arg2: TACSymbol
    ): List<TACCmd.Simple> {

        val nanV = vFac.mkFreshIntVar()
        val infV = vFac.mkFreshIntVar()
        val finiteV = vFac.mkFreshIntVar()
        val nonZeroFiniteV = vFac.mkFreshIntVar()

        return  nondetWithAssumptions(nanV, listOf(isf64NaN(nanV))) +
                nondetWithAssumptions(infV, listOf(isf64Inf(infV))) +
                nondetWithAssumptions(finiteV, listOf(isFinite(finiteV))) +
                nondetWithAssumptions(nonZeroFiniteV,
                    listOf(
                        isFinite(nonZeroFiniteV), isf64NonZero(nonZeroFiniteV), isf64NonSubnormal(nonZeroFiniteV)
                    )
                ) +
                assign(res,
                    sbfTacB {
                        switch(
                            isf64NaN(arg1) or isf64NaN(arg2) to nanV.asSym(),
                            (isf64Inf(arg1) and isf64Zero(arg2)) or (isf64Zero(arg1) and isf64NaN(arg2)) to nanV.asSym(),
                            isf64Inf(arg1) or isf64Inf(arg2)  to infV.asSym(),
                            isf64Zero(arg1) to arg1.asSym(),
                            isf64Zero(arg2) to arg2.asSym(),
                            isf64NonSubnormal(arg1) and isf64NonSubnormal(arg2) to nonZeroFiniteV.asSym(),
                            default = finiteV.asSym()
                        )
                    }
                )

    }

    context(SbfCFGToTAC<TNum, TOffset, TFlags>)
    internal fun summarizeDivdf3(
        res: TACSymbol.Var,
        @Suppress("UNUSED_PARAMETER")
        arg1: TACSymbol,
        @Suppress("UNUSED_PARAMETER")
        arg2: TACSymbol
    ): List<TACCmd.Simple> = listOf(havoc(res))


    context(SbfCFGToTAC<TNum, TOffset, TFlags>)
    internal fun summarizeNegdf3(
        res: TACSymbol.Var,
        @Suppress("UNUSED_PARAMETER")
        arg: TACSymbol
    ): List<TACCmd.Simple> = listOf(havoc(res))

    /**
     * Convert [arg] as f64 to u64
     *
     * ```
     * if isNaN(arg) || arg == 0 || isNegative(arg) || isSubnormal(arg) {
     *    0
     * } else {
     *    res = nondet()
     *    assume(res != 0)
     *    res
     *  }
     * ```
     */
    context(SbfCFGToTAC<TNum, TOffset, TFlags>)
    internal fun summarizeFixunsdfdi(
        res: TACSymbol.Var,
        arg: TACSymbol
    ): List<TACCmd.Simple> {
        // `defaultV` models a u64 number
        val nonZeroV  = vFac.mkFreshIntVar()
        return nondetWithAssumptions(nonZeroV, listOf(sbfTacB { nonZeroV neq sbfTacB.ZERO})) +
               assign(res,
                   sbfTacB {
                       switch(
                           isf64Zero(arg) or isf64NaN(arg) or isf64Negative(arg) or isf64Subnormal(arg) to ZERO,
                           default = nonZeroV.asSym()
                       )
                   }
                )
    }

    /**
     * Convert [arg] as u64 to f64
     *
     * ```
     * if (arg == 0) {
     *    arg
     * } else {
     *    res = nondet()
     *    assume(res != 0)
     *    assume(res != NaN)
     *    assume(res != Inf)
     *    res
     *  }
     * ```
     */
    context(SbfCFGToTAC<TNum, TOffset, TFlags>)
    internal fun summarizeFloatundidf(
        res: TACSymbol.Var,
        arg: TACSymbol
    ): List<TACCmd.Simple> {

        // `zeroV` and `defaultV` model f64 numbers
        val (zeroV, defaultV) = listOf(vFac.mkFreshIntVar(), vFac.mkFreshIntVar())
        return  nondetWithAssumptions(
                    defaultV,
                    listOf(isf64NonZero(defaultV), isNotf64NaN(defaultV), isNotf64Inf(defaultV), isf64NonSubnormal(defaultV))
                ) +
                nondetWithAssumptions(zeroV, listOf(isf64Zero(zeroV))) +
                assign(res,
                    sbfTacB {
                        switch(
                            arg eq sbfTacB.ZERO to zeroV.asSym(),
                            default = defaultV.asSym()
                        )
                    }
                )
    }

    /** Return zero if neither argument is NaN, and [arg1] and [arg2] are equal. **/
    context(SbfCFGToTAC<TNum, TOffset, TFlags>)
    internal fun summarizeEqdf2(
        res: TACSymbol.Var,
        arg1: TACSymbol,
        arg2: TACSymbol
    ): List<TACCmd.Simple> {
        // `trueS` represents a u64 number
        val trueS = sbfTacB.ZERO
        // `falseV` represents a u64 number
        val falseV = vFac.mkFreshIntVar()
        return nondetWithAssumptions(falseV, listOf(sbfTacB { falseV.asSym() neq trueS })) +
            assign(res,
                sbfTacB {
                    switch(
                        isf64NaN(arg1) or isf64NaN(arg2) to falseV.asSym(),
                        // +0 and -0 are equal
                        (isf64PlusZero(arg1) and isf64MinusZero(arg2)) or (isf64MinusZero(arg1) and isf64PlusZero(arg2)) to trueS,
                        arg1 eq arg2  to trueS,
                        default = falseV.asSym()
                    )
                }
            )
    }

    /** Return a nonzero value if either argument is NaN, or if [arg1] and [arg2] are unequal **/
    context(SbfCFGToTAC<TNum, TOffset, TFlags>)
    internal fun summarizeNedf2(
        res: TACSymbol.Var,
        arg1: TACSymbol,
        arg2: TACSymbol
    ): List<TACCmd.Simple> {
        // `trueV` represents a u64 number
        val trueV = vFac.mkFreshIntVar()
        // `falseS` represents a u64 number
        val falseS = sbfTacB.ZERO
        return  nondetWithAssumptions(trueV, listOf(sbfTacB { trueV.asSym() neq falseS })) +
            assign(res,
                sbfTacB {
                    switch(
                        // +0 and -0 are equal
                        (isf64PlusZero(arg1) and isf64MinusZero(arg2)) or (isf64MinusZero(arg1) and isf64PlusZero(arg2)) to falseS,
                        isf64NaN(arg1) or isf64NaN(arg2) or (arg1 neq arg2) to trueV.asSym(),
                        default = falseS
                    )
                }
            )
    }

    /** Return a value less than zero if neither argument is NaN, and [arg1] is strictly less than [arg2]. **/
    context(SbfCFGToTAC<TNum, TOffset, TFlags>)
    internal fun summarizeLtdf2(
        res: TACSymbol.Var,
        arg1: TACSymbol,
        arg2: TACSymbol
    ): List<TACCmd.Simple> {
        // `trueV` and `falseV` represent u64 numbers
        val (trueV, falseV) = vFac.mkFreshIntVar() to vFac.mkFreshIntVar()
        return  nondetWithAssumptions(trueV, listOf(sbfTacB { trueV.asSym() sLt ZERO})) +
            nondetWithAssumptions(falseV, listOf(sbfTacB { falseV.asSym() sGe ZERO})) +
            summarizeBinRel(res, arg1, arg2,
                eitherNaN = falseV.asSym(),
                bothZero = falseV.asSym(),
                firstZero = trueV.asSym(),
                secondZero = falseV.asSym()
            )
    }

    /** Return a value less than or equal to zero if neither argument is NaN, and [arg1] is less than or equal to [arg2] **/
    context(SbfCFGToTAC<TNum, TOffset, TFlags>)
    internal fun summarizeLedf2(
        res: TACSymbol.Var,
        arg1: TACSymbol,
        arg2: TACSymbol
    ): List<TACCmd.Simple> {
        // `trueV` and `falseV` represent u64 numbers
        val (trueV, falseV) = vFac.mkFreshIntVar() to vFac.mkFreshIntVar()
        return  nondetWithAssumptions(trueV, listOf(sbfTacB { trueV.asSym() sLe ZERO})) +
            nondetWithAssumptions(falseV, listOf(sbfTacB { falseV.asSym() sGt ZERO})) +
            summarizeBinRel(res, arg1, arg2,
                eitherNaN = falseV.asSym(),
                bothZero = trueV.asSym(),
                firstZero = trueV.asSym(),
                secondZero = falseV.asSym()
            )
    }

    /**
     * return a value greater than or equal to zero if neither argument is NaN, and [arg1] is greater than or equal to [arg2].
     **/
    context(SbfCFGToTAC<TNum, TOffset, TFlags>)
    internal fun summarizeGedf2(
        res: TACSymbol.Var,
        arg1: TACSymbol,
        arg2: TACSymbol
    ): List<TACCmd.Simple> {
        // `trueV` and `falseV` represent u64 numbers
        val (trueV, falseV) = vFac.mkFreshIntVar() to vFac.mkFreshIntVar()
        return  nondetWithAssumptions(trueV, listOf(sbfTacB { trueV.asSym() sGe ZERO})) +
            nondetWithAssumptions(falseV, listOf(sbfTacB { falseV.asSym() sLt ZERO})) +
            summarizeBinRel(res, arg1, arg2,
                eitherNaN = falseV.asSym(),
                bothZero = trueV.asSym(),
                firstZero = falseV.asSym(),
                secondZero = trueV.asSym()
            )
    }

    /**
     * Return a value greater than zero if neither argument is NaN, and [arg1] is strictly greater than [arg2].
     */
    context(SbfCFGToTAC<TNum, TOffset, TFlags>)
    internal fun summarizeGtdf2(
        res: TACSymbol.Var,
        arg1: TACSymbol,
        arg2: TACSymbol
    ): List<TACCmd.Simple> {
        // `trueV` and `falseV` represent u64 numbers
        val (trueV, falseV) = vFac.mkFreshIntVar() to vFac.mkFreshIntVar()
        return  nondetWithAssumptions(trueV, listOf(sbfTacB { trueV.asSym() sGt  ZERO})) +
                nondetWithAssumptions(falseV, listOf(sbfTacB { falseV.asSym() sLe ZERO})) +
                summarizeBinRel(res, arg1, arg2,
                    eitherNaN = falseV.asSym(),
                    bothZero = falseV.asSym(),
                    firstZero = falseV.asSym(),
                    secondZero = trueV.asSym()
                )
    }

    /**
     * This is a generic summarizer for a binary relational operators: `lt`, `le`, `gt`, and `ge`.
     *
     * ```
     * return if isNaN(arg1) || isNaN(arg2)
     *     eitherNaN
     * if arg1 == 0 && arg2 == 0
     *     bothZero
     * if arg1 == 0
     *     firstZero
     * if arg2 == 0
     *     secondZero
     * else
     *     nondet
     * ```
     * @param [arg1] represents a f64 number.
     * @param [arg2] represents a f64 number.
     * @param [eitherNaN] represents a u64 number.
     * @param [bothZero] represents a u64 number.
     * @param [firstZero] represents a u64 number.
     * @param [secondZero] represents a u64 number.
     **/
    context(SbfCFGToTAC<TNum, TOffset, TFlags>)
    private fun summarizeBinRel(
        res: TACSymbol.Var,
        arg1: TACSymbol,
        arg2: TACSymbol,
        eitherNaN: TACExpr.Sym.Var,
        bothZero: TACExpr.Sym.Var,
        firstZero: TACExpr.Sym.Var,
        secondZero: TACExpr.Sym.Var
    ): List<TACCmd.Simple> {

        // `nondetV` represents a u64 number
        val nondetV = vFac.mkFreshIntVar()
        return  nondetWithAssumptions(nondetV) +
            assign(res,
                sbfTacB {
                    switch(
                        isf64NaN(arg1) or isf64NaN(arg1) to eitherNaN,
                            isf64Zero(arg1) and isf64Zero(arg1) to bothZero,
                            isf64Zero(arg1) to firstZero,
                            isf64Zero(arg2) to secondZero,
                        default = nondetV.asSym()
                    )
                }
            )
    }
}
