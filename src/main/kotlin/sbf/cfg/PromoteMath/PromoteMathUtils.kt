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

import sbf.disassembler.SbfRegister

/**
 * Returns true if [reg] might be read before being written at any position strictly after [afterPos].
 */
internal fun isMayLiveAfter(bb: SbfBasicBlock, reg: Value.Reg, afterPos: Int): Boolean {
    val insts = bb.getInstructions()
    for (pos in afterPos + 1 until insts.size) {
        val inst = insts[pos]
        if (inst.writeRegister.contains(reg)) {
            return false
        }
        if (inst.readRegisters.contains(reg)) {
            return true
        }
    }
    return true // conservative because we don't check beyond bb. For that we need to ask a liveness analysis
}

/**
 * Scan positions `[firstPos, lastPos]` and collects non-pattern store instructions whose
 * stored value is matches by the predicate [storedValueMatches].  Returns `null` if any
 * other non-pattern store is found, otherwise returns the list of store instructions.
 */
internal fun collectTrailingStores(
    bb: SbfBasicBlock,
    insts: List<SbfInstruction>,
    firstPos: Int,
    lastPos: Int,
    patternPositions: Set<Int>,
    mayWriteToI128Result: (SbfInstruction.Mem) -> Boolean
): List<LocatedSbfInstruction>? {
    val trailingStoreLocInsts = mutableListOf<LocatedSbfInstruction>()
    for (pos in firstPos..lastPos) {
        if (pos in patternPositions) {
            continue
        }
        val nonPatternInst = insts[pos]
        val nonPatternLocInst = LocatedSbfInstruction(bb.getLabel(), pos, nonPatternInst)
        if (nonPatternInst is SbfInstruction.Mem && !nonPatternInst.isLoad) {
            if(mayWriteToI128Result(nonPatternInst)){
                trailingStoreLocInsts.add(nonPatternLocInst)
            } else {
                return null
            }
        }
    }
    return trailingStoreLocInsts
}

/**
 * Resolves an input operand [reg] that is first read by a pattern instruction at [firstUsedAtPos].
 *
 * If no non-pattern instruction in `(firstUsedAtPos, lastPos)` writes [reg], the value in [reg]
 * at the call site (which is placed near [lastPos]) is still the expected input value, so we
 * return [RegOrStack.Reg].
 *
 * If such a clobbering instruction exists, the register will hold the wrong value at the call
 * site. We then scan backwards from [firstUsedAtPos] to find the instruction that defined [reg]'s
 * value, and return [RegOrStack.Stack] if it is stack load, allowing [lowerImpl]
 * to reload the value directly from the stack slot instead.  Returns null if the defining
 * instruction is not a stack load (caller should skip the pattern in that case).
 */
internal fun resolveInputParam(
    reg: Value.Reg,
    firstUsedAtPos: Int,
    patternPositions: Set<Int>,
    lastPos: Int,
    insts: List<SbfInstruction>
): RegOrStack? {
    val clobbered = (firstUsedAtPos + 1 until lastPos).any { k ->
        k !in patternPositions && insts[k].writeRegister.contains(reg)
    }

    if (!clobbered) {
        return RegOrStack.Reg(reg)
    }

    // The register is overwritten after its first use; find its definition.
    for (pos in firstUsedAtPos - 1 downTo 0) {
        val inst = insts[pos]
        if (!inst.writeRegister.contains(reg)) {
            continue
        }
        val memInst = inst as? SbfInstruction.Mem ?: return null
        if (!memInst.isLoad) {
            return null
        }
        if (memInst.access.base != Value.Reg(SbfRegister.R10)) {
            return null
        }
        return RegOrStack.Stack(memInst.access)
    }
    return null
}

/**
 * Find the last instruction that writes to [dst] strictly before position [before] in [bb],
 * and returns it if [predicate] holds for it, otherwise returns null.
 */
fun findLastDefinition(
    bb: SbfBasicBlock,
    dst: Value.Reg,
    before: Int,
    predicate: (LocatedSbfInstruction) -> Boolean
): LocatedSbfInstruction? {
    val insts = bb.getInstructions()
    for (pos in before - 1 downTo 0) {
        val inst = insts[pos]
        if (!inst.writeRegister.contains(dst)) {
            continue
        }
        val locInst = LocatedSbfInstruction(bb.getLabel(), pos, inst)
        return if (predicate(locInst)) {
            locInst
        } else {
            null
        }
    }
    return null
}

/**
 * Scan forward from [afterPos] and return the first instruction for which [match] holds.
 * Return null if [stop] holds before a match is found.
 */
fun findFirstAfter(
    bb: SbfBasicBlock,
    afterPos: Int,
    match: (LocatedSbfInstruction) -> Boolean,
    stop: (LocatedSbfInstruction) -> Boolean
): LocatedSbfInstruction? {
    val insts = bb.getInstructions()
    for (pos in afterPos + 1 until insts.size) {
        val locInst = LocatedSbfInstruction(bb.getLabel(), pos, insts[pos])
        if (match(locInst)) {
            return locInst
        }
        if (stop(locInst)) {
            return null
        }
    }
    return null
}
