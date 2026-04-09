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
import sbf.SolanaConfig
import sbf.callgraph.CVTNondet
import sbf.cfg.SbfInstruction
import sbf.disassembler.SbfRegister
import sbf.domains.*
import vc.data.TACCmd
import java.math.BigInteger

/** Emit TAC code for nondet functions **/
context(SbfCFGToTAC<TNum, TOffset, TFlags>)
internal fun<TNum : INumValue<TNum>, TOffset : IOffset<TOffset>, TFlags: IPTANodeFlags<TFlags>> summarizeNondet(
    nondetFn: CVTNondet, inst: SbfInstruction.Call
): List<TACCmd.Simple> {
    when (nondetFn) {
        CVTNondet.NONDET_I8, CVTNondet.NONDET_I16, CVTNondet.NONDET_I32, CVTNondet.NONDET_I64 -> {
            val r0 = sbfTacB.mkVar(SbfRegister.R0)
            val bits = when (nondetFn) {
                CVTNondet.NONDET_I8  ->  8
                CVTNondet.NONDET_I16 ->  16
                CVTNondet.NONDET_I32 ->  32
                CVTNondet.NONDET_I64 ->  64
                else -> throw TACTranslationError("Unexpected CVT_nondet signed integer function ${inst.name}")
            }
            val n = BigInteger.TWO.pow(if (SolanaConfig.UseTACSignedMath.get()) { bits }  else { bits - 1 })
            val rangeAssume = if (SolanaConfig.UseTACSignedMath.get()) {
                // if this flag is enabled then range similar to unsigned counterparts
                inRange(r0, BigInteger.ZERO, n, true)
            } else {
                inRange(r0, -n, n, false)
            }
            return listOf(Debug.externalCall(inst),
                   havoc(r0)) +
                   rangeAssume +
                   listOf(Calltrace.externalCall(inst, listOf(r0)))
        }
        CVTNondet.NONDET_U8, CVTNondet.NONDET_U16, CVTNondet.NONDET_U32, CVTNondet.NONDET_U64, CVTNondet.NONDET_USIZE -> {
            val r0 = sbfTacB.mkVar(SbfRegister.R0)
            val n = when (nondetFn) {
                CVTNondet.NONDET_U8  -> BigInteger.TWO.pow(8)
                CVTNondet.NONDET_U16 -> BigInteger.TWO.pow(16)
                CVTNondet.NONDET_U32 -> BigInteger.TWO.pow(32)
                CVTNondet.NONDET_U64, CVTNondet.NONDET_USIZE -> {
                    /// usize is the size of a pointer
                    BigInteger.TWO.pow(64)
                }
                else -> throw TACTranslationError("Unexpected CVT_nondet unsigned integer function ${inst.name}")
            }
            return listOf(
                    Debug.externalCall(inst),
                    havoc(r0)
                    ) +
                    inRange(r0, BigInteger.ZERO, n) +
                    Calltrace.externalCall(inst, listOf(r0))
        }
    }
}
