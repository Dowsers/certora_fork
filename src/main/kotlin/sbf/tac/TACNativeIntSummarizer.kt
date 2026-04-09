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

import cvlr.CvlrFunctions
import datastructures.stdcollections.listOf
import sbf.callgraph.CVTNativeInt
import sbf.cfg.LocatedSbfInstruction
import sbf.cfg.SbfInstruction
import sbf.disassembler.SbfRegister
import sbf.domains.INumValue
import sbf.domains.IOffset
import sbf.domains.IPTANodeFlags
import sbf.domains.SbfType
import vc.data.TACCmd

/**
 * Summarize nativeint intrinsics
 *
 * These intrinsics allow users to write specifications using native integers.
 * Currently, we use 256-bit TAC variables to simulate nativeint.
 */
context(SbfCFGToTAC<TNum, TOffset, TFlags>)
internal fun <TNum : INumValue<TNum>, TOffset : IOffset<TOffset>, TFlags: IPTANodeFlags<TFlags>> summarizeNativeInt(
    locInst: LocatedSbfInstruction
): List<TACCmd.Simple> {
    val inst = locInst.inst
    check(inst is SbfInstruction.Call) {"summarizeNativeInt expects a call instruction instead of ${locInst.inst}"}
    val function = CVTNativeInt.from(inst.name)
    check(function != null) {"summarizeNativeInt does not support ${inst.name}"}

    // These symbols are created using 256-bit
    val r1 = natIntTacB.mkVar(SbfRegister.R1).asSym()
    val r2 = natIntTacB.mkVar(SbfRegister.R2).asSym()
    val r3 = natIntTacB.mkVar(SbfRegister.R3).asSym()
    val r4 = natIntTacB.mkVar(SbfRegister.R4).asSym()
    val r0 = natIntTacB.mkVar(SbfRegister.R0)
    val zero = natIntTacB.ZERO
    val one  = natIntTacB.ONE

    return listOf(
        when (function) {
            CVTNativeInt.NATIVEINT_EQ -> assign(r0, natIntTacB { ite (r1 eq r2, one, zero)})
            CVTNativeInt.NATIVEINT_LT -> assign(r0, natIntTacB { ite(r1 lt r2, one, zero) })
            CVTNativeInt.NATIVEINT_LE -> assign(r0, natIntTacB { ite(r1 le r2, one, zero) })
            CVTNativeInt.NATIVEINT_SLT -> assign(r0, natIntTacB { ite(r1 sLt r2, one, zero) })
            CVTNativeInt.NATIVEINT_SLE -> assign(r0, natIntTacB { ite(r1 sLe r2, one, zero) })
            CVTNativeInt.NATIVEINT_ADD -> assign(r0, natIntTacB { r1 add r2 })
            CVTNativeInt.NATIVEINT_SUB -> assign(r0, natIntTacB { r1 sub r2 })
            CVTNativeInt.NATIVEINT_MUL -> assign(r0, natIntTacB { r1 mul r2 })
            CVTNativeInt.NATIVEINT_DIV -> assign(r0, natIntTacB { r1 div r2 })
            CVTNativeInt.NATIVEINT_CEIL_DIV -> assign(r0, natIntTacB { r1 ceilDiv r2})
            CVTNativeInt.NATIVEINT_MULDIV -> assign(r0, natIntTacB.MulDiv(r1,r2,r3))
            CVTNativeInt.NATIVEINT_MULDIV_CEIL -> assign(r0, natIntTacB.MulDivCeil(r1,r2,r3))
            CVTNativeInt.NATIVEINT_NONDET -> havoc(r0)
            CVTNativeInt.NATIVEINT_FROM_U128 ->
                /**
                 *  build a nativeint from u128 (two 64-bit registers: r1:low, r2:high)
                 **/
                assign(r0, natIntTacB.mergeU128(r1, r2, false))
            CVTNativeInt.NATIVEINT_FROM_U256 ->
                /**
                 * build a nativeint from u256 (four 64-bit registers)
                 **/
                assign(r0, natIntTacB.mergeU256(r1, r2, r3, r4, false))
            CVTNativeInt.NATIVEINT_U64_MAX -> assign(r0, natIntTacB.U64_MAX)
            CVTNativeInt.NATIVEINT_U128_MAX -> assign(r0, natIntTacB.U128_MAX)
            CVTNativeInt.NATIVEINT_U256_MAX -> assign(r0, natIntTacB.U256_MAX)
            CVTNativeInt.NATIVEINT_SEXT -> {
                // nativeint_u64_sext(val, from_width) returns
                //   if from_width=8   -> signExtToBv256(val & 0xFF, 8)
                //   if from_width=16  -> signExtToBv256(val & 0xFFFF, 16)
                //   if from_width=32  -> signExtToBv256(val & 0xFFFF_FFFF, 32)
                //   if from_width=64  -> signExtToBv256(val & 0xFFFF_FFFF_FFFF_FFFF, 64)
                //   if from_width=128 -> signExtToBv256(val & 0xFFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF, 128)
                val fromWidth = (types.typeAtInstruction(locInst, SbfRegister.R2) as? SbfType.NumType)?.value?.toLongOrNull()
                    ?: throw TACTranslationError(
                        "${CvlrFunctions.CVT_nativeint_u64_sext} expects width to be statically known as a constant number"
                    )
                assign(r0, natIntTacB.signExtendSbfValueWithMask(r1, fromWidth))
            }
            CVTNativeInt.NATIVEINT_NEG -> assign(r0, natIntTacB.ModNeg(r1))
            CVTNativeInt.NATIVEINT_MASK -> {
                // nativeint_mask(val, bits) returns val & ((1 << bits) - 1)
                val bits = (types.typeAtInstruction(locInst, SbfRegister.R2) as? SbfType.NumType)?.value?.toLongOrNull()
                    ?: throw TACTranslationError(
                        "${CvlrFunctions.CVT_nativeint_u64_mask} expects bits to be statically known as a constant number"
                    )
                assign(r0, natIntTacB.mask(r1, bits))
            }

        }
    )
}
