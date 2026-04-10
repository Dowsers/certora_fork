/*
 *     The Certora Prover
 *     Copyright (C) 2026  Certora Ltd.
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

package sbf.cfg

import cvlr.CvlrFunctions
import datastructures.stdcollections.*
import log.Logger
import log.LoggerTypes

private val logger = Logger(LoggerTypes.SBF_MATH_PROMOTION)
private fun dbg(msg: () -> Any) {
    logger.info(msg)
}

data class U128GtPattern(
    override val intrinsicName: String,
    override val instructions: List<LocatedSbfInstruction>,
    val params: Int128BinaryParams,
    val result: Int128OperationResult.SingleResult,
    /** Non-pattern store instructions interleaved between the pattern instructions that store
     *  the result. They are removed along with the pattern instructions and re-emitted
     *  verbatim after the gt call so they read the correct result value. */
    val trailingStores: List<SbfInstruction> = emptyList()
) : MathIntrinsicPattern

/** Replace u128 greater-than comparison patterns with calls to `CVT_u128_gt` **/
val U128GtTransform = object : MathIntrinsicsTransform<U128GtPattern> {
    override val name: String = CvlrFunctions.CVT_u128_gt

    /**
     * Scans for u128 greater-than patterns inside [bb] and returns the matched
     * instructions paired with their parameters.
     *
     * The pattern represents the computation (xLow:xHigh) > (yLow:yHigh) using select instructions.
     *
     * We detect the pattern:
     *
     * ```
     *   (1) tmpLow = select(xLow ugt yLow, 1, 0)    // low comparison
     *   (2) tmpHigh = select(xHigh ugt yHigh, 1, 0) // high comparison
     *   (3) result = select(xHigh eq yHigh, tmpLow, tmpHigh) // combine
     * ```
     *
     * Note: The result register can be the same as tmpLow or tmpHigh (in-place update).
     * The result register contains 1 if (xLow:xHigh) > (yLow:yHigh), 0 otherwise.
     */
    override fun matchInBlock(
        bb: SbfBasicBlock,
        equalAt: (LocatedSbfInstruction, Value, Value.Reg) -> Boolean
    ): List<U128GtPattern> {
        dbg { "=== Starting U128Gt pattern matching in block ${bb.getLabel()} ===" }
        dbg { "=== Block $bb ===" }
        val res = mutableListOf<U128GtPattern>()
        val insts = bb.getInstructions()
        val locInsts = bb.getLocatedInstructions()

        // Try to match the 3-select pattern for u128 greater-than
        // result = select(xHigh eq yHigh, tmpLow, tmpHigh)
        for (i3 in locInsts.indices) {
            val locInst3 = locInsts[i3]
            val inst3 = locInst3.inst as? SbfInstruction.Select ?: continue

            // Final select must be an equality check
            val cond3 = inst3.cond
            if (cond3.op != CondOp.EQ) {
                continue
            }

            val tmpLow = inst3.trueVal as? Value.Reg ?: continue
            val tmpHigh = inst3.falseVal as? Value.Reg ?: continue
            val result = inst3.dst
            val p3 = locInst3.pos

            dbg { "[3] $inst3" }

            val p1Sel = matchSelect(bb, tmpLow, p3) { sel ->
                sel.cond.op == CondOp.GT && sel.cond.right is Value.Reg
            } ?: continue

            dbg { "[1] $p1Sel xLow: ${p1Sel.x}, yLow: ${p1Sel.y}" }
            val p2Sel = matchSelect(bb, tmpHigh, p3) { sel ->
                // Both select operations must have the same op
                p1Sel.op == sel.cond.op && sel.cond.right is Value.Reg
            } ?: continue
            dbg { "[2] $p2Sel xHigh: ${p2Sel.x}, yHigh: ${p2Sel.y}" }

            val p1 = p1Sel.locIns.pos
            val xLow = p1Sel.x
            val yLow = p1Sel.y
            val xHigh = p2Sel.x
            val yHigh = p2Sel.y
            val p2 = p2Sel.locIns.pos
            val lastPos = maxOf(p1, p2, p3)
            val firstPos = minOf(p1, p2, p3)

            // Resolve parameters
            val patternPositions = setOf(p1, p2, p3)
            val xLowParam = resolveInputParam(xLow, p1, patternPositions, lastPos, insts) ?: continue
            val xHighParam = resolveInputParam(xHigh, p2, patternPositions, lastPos, insts) ?: continue
            val yLowParam = resolveInputParam(yLow, p1, patternPositions, lastPos, insts) ?: continue
            val yHighParam = resolveInputParam(yHigh, p2, patternPositions, lastPos, insts) ?: continue


            dbg { "Detected compact u128_gt: result=$result" }

            val trailingStoreLocInsts = collectTrailingStores(bb, insts, firstPos, lastPos, patternPositions) { memInstruction ->
                check(!memInstruction.isLoad){ "Expected a store memory instruction" }
                memInstruction.value == result
            } ?: continue
            val newPattern = U128GtPattern(
                intrinsicName = CvlrFunctions.CVT_u128_gt,
                instructions = (listOf(
                    p2Sel.locIns,
                    p1Sel.locIns,
                    locInst3
                ) + trailingStoreLocInsts).sortedBy { it.pos },
                params = Int128BinaryParams(xLowParam, xHighParam, yLowParam, yHighParam),
                result = Int128OperationResult.SingleResult(result),
                trailingStores = trailingStoreLocInsts.map { it.inst }
            )

            dbg { "Compact Pattern: $newPattern" }

            res.add(newPattern)
        }

        return res
    }

    override fun lower(pattern: U128GtPattern, useDynFrames: Boolean) =
        lowerImpl(pattern.intrinsicName, pattern.params, pattern.result, useDynFrames) + pattern.trailingStores

    override fun abstractStateFilter(locInst: LocatedSbfInstruction): Boolean {
        return false
    }

    /**
     * Finds a select instruction with the given dst register and true/false values.
     */
    private fun matchSelect(
        bb: SbfBasicBlock,
        dst: Value.Reg,
        beforePos: Int = Int.MAX_VALUE,
        predicate: (SbfInstruction.Select) -> Boolean
    ): SelectIns? {
        val locIns = findLastDefinition(bb, dst, beforePos) { locInst ->
            val inst = locInst.inst
            inst is SbfInstruction.Select &&
                (inst.trueVal as? Value.Imm)?.v == 1UL &&
                (inst.falseVal as? Value.Imm)?.v == 0UL &&
                predicate(inst)
        } ?: return null

        val ins = locIns.inst as SbfInstruction.Select
        val (x, y) = when (ins.cond.op) {
            CondOp.GE -> {
                ins.cond.right as Value.Reg to ins.cond.left
            }

            CondOp.GT -> {
                ins.cond.left to ins.cond.right as Value.Reg
            }

            else -> error("Only ${CondOp.GT} or ${CondOp.GE} are allowed here.")
        }
        return SelectIns(locIns, ins.cond.op, x, y)
    }
}

private data class SelectIns(
    val locIns: LocatedSbfInstruction,
    val op: CondOp,
    val x: Value.Reg,
    val y: Value.Reg
)
