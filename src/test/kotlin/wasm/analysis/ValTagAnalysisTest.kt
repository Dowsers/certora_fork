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
 *     MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 *     GNU General Public License for more details.
 *
 *     You should have received a copy of the GNU General Public License
 *     along with this program.  If not, see <https://www.gnu.org/licenses/>.
 */

package wasm.analysis

import analysis.CommandFinderMixin
import analysis.MockStackVarMixin
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTrue
import testing.ttl.TACMockLanguage
import org.junit.jupiter.api.Test
import vc.data.TACBuilderAuxiliaries
import wasm.host.soroban.Val
import wasm.host.soroban.analysis.ValTagAnalysis

class ValTagAnalysisTest: MockStackVarMixin, CommandFinderMixin, TACBuilderAuxiliaries() {
    @Test
    fun testSimpleTag() {
        val cfg = TACMockLanguage.make {
            L1020 = "BWAnd( L1021:bv256 0xFF )"
            tagNext("here")
            L1021 = `*`
            tagNext("there")
            L1023 = `*`
        }
        val here = cfg.findCommandOrFail("here")
        val there = cfg.findCommandOrFail("there")
        val tags = cfg.cache.get(ValTagAnalysis)
        assertEquals(setOf(L1020), tags.eqTagsOf(here, L1021))
        assertTrue(tags.eqTagsOf(there, L1021)?.isEmpty() == true)
    }

    @Test
    fun testTagBranching() {
        val cfg = TACMockLanguage.make {
            L1020 = `*`
            L1021 = "BWAnd( L1020 0xFF )"
            L1022 = "Eq( L1021 0x4D )"
            `if`(L(1022)) {
                tagNext("one")
                L1023 = `*`
            }`else`{
                tagNext("two")
                L1023 = `*`
            }
            tagNext("three")
            L1021 = `*`
        }
        val one = cfg.findCommandOrFail("one")
        val two = cfg.findCommandOrFail("two")
        val three = cfg.findCommandOrFail("two")
        val tags = cfg.cache.get(ValTagAnalysis)
        assertEquals(setOf(Val.Tag(0x4D)), tags.tagSet(one, L1020))
        assertEquals(null, tags.tagSet(two, L1020))
        assertEquals(null, tags.tagSet(three, L1020))
        assertEquals(setOf(L1021), tags.eqTagsOf(three, L1020))
    }

    @Test
    fun testTagJoins() {
        val cfg = TACMockLanguage.make {
            L1020 = `*`
            L1021 = "BWAnd( L1020 0xFF )"
            L1022 = "Eq( L1021 0x4D )"
            `if`(L(1022)) {
                L1023 = `*`
            }`else`{
                L1022 = "Eq( L1021 0x09 )"
                `if`(L(1022)) {

                }`else`{
                    exit()
                }
            }
            tagNext("here")
            L1021 = `*`
        }
        val here = cfg.findCommandOrFail("here")
        val tags = cfg.cache.get(ValTagAnalysis)
        assertEquals(
            setOf(Val.Tag(0x4D), Val.Tag(0x09)),
            tags.tagSet(here, L1020)
        )
    }
}
