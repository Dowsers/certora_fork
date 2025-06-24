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

package normalizer

import analysis.CommandWithRequiredDecls
import analysis.maybeExpr
import analysis.maybeNarrow
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test
import tac.StartBlock
import tac.Tag
import utils.*
import vc.data.*
import vc.data.TACProgramCombiners.toCore

class SpillRewriterTest {

    @Test
    fun testBasicRewriting() {
        val scalar = TACKeyword.TMP(Tag.Bit256, "boop").toUnique("!")
        val prog = CommandWithRequiredDecls(listOf(
            TACCmd.Simple.AssigningCmd.AssignExpCmd(
                lhs = TACKeyword.MEM64.toVar(),
                rhs = 0x100.asTACExpr
            ),
            TACCmd.Simple.AssigningCmd.ByteStore(
                base = TACKeyword.MEMORY.toVar(),
                loc = 0x80.asTACSymbol(),
                value = 0x20.asTACSymbol()
            ),

            TACCmd.Simple.AssigningCmd.ByteLoad(
                lhs = scalar,
                loc = 0x80.asTACSymbol(),
                base = TACKeyword.MEMORY.toVar()
            )
        ), setOf(scalar, TACKeyword.MEM64.toVar(), TACKeyword.MEMORY.toVar())).toCore("simple", StartBlock)
        val rewritten = OptimisticSpillRewriter.rewrite(prog)
        Assertions.assertTrue(rewritten.parallelLtacStream().mapNotNull {
            it.maybeNarrow<TACCmd.Simple.AssigningCmd.AssignExpCmd>()?.takeIf { it.cmd.lhs == scalar }
        }.mapNotNull {
            it.wrapped.maybeExpr<TACExpr.Sym.Var>()?.exp?.s?.meta?.contains(OptimisticSpillRewriter.SPILL_VARIABLE)
        }.findFirst().orElse(false)) {
            "Did not find scalar assignment"
        }
        Assertions.assertTrue(rewritten.parallelLtacStream().anyMatch { it.cmd is TACCmd.Simple.AssertCmd }) {
            "Did not find instrumented assertion"
        }
        Assertions.assertTrue(rewritten.parallelLtacStream().anyMatch {
            it.cmd is TACCmd.Simple.AssigningCmd.ByteLoad && OptimisticSpillRewriter.VALIDATION_READ in it.cmd.meta
        })
    }

    @Test
    fun rewritingIsConservative() {
        val scalar = TACKeyword.TMP(Tag.Bit256, "boop").toUnique("!")
        val prog = CommandWithRequiredDecls(listOf(
            TACCmd.Simple.AssigningCmd.AssignExpCmd(
                lhs = TACKeyword.MEM64.toVar(),
                rhs = 0x100.asTACExpr
            ),
            TACCmd.Simple.AssigningCmd.ByteStore(
                base = TACKeyword.MEMORY.toVar(),
                loc = 0x80.asTACSymbol(),
                value = 0x20.asTACSymbol()
            ),
            TACCmd.Simple.AssigningCmd.ByteStore(
                base = TACKeyword.MEMORY.toVar(),
                loc = 0x80.asTACSymbol(),
                value = 0x40.asTACSymbol()
            ),

            TACCmd.Simple.AssigningCmd.ByteLoad(
                lhs = scalar,
                loc = 0x80.asTACSymbol(),
                base = TACKeyword.MEMORY.toVar()
            )
        ), setOf(scalar, TACKeyword.MEM64.toVar(), TACKeyword.MEMORY.toVar())).toCore("simple", StartBlock)
        val rewritten = OptimisticSpillRewriter.rewrite(prog)
        Assertions.assertTrue(rewritten.parallelLtacStream().anyMatch {
            it.maybeNarrow<TACCmd.Simple.AssigningCmd.ByteLoad>()?.cmd?.lhs == scalar
        }) {
            "Byteload got incorrectly rewritten"
        }
    }
}
