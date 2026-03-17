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

package sbf

import sbf.cfg.*
import sbf.testing.SbfTestDSL
import org.junit.jupiter.api.*
import sbf.support.UnknownStackPointerError
import sbf.tac.TACTranslationError

class TACNativeIntTest {

    @Test
    fun test1() {
        val cfg = SbfTestDSL.makeCFG("test1") {
            bb(0) {
                r1 = 3
                r2 = 2
                "CVT_nativeint_u64_div_ceil"()
                r1 = r0
                r2 = 2
                "CVT_nativeint_u64_eq"()
                assert(CondOp.EQ(r0, 1))
                exit()
            }
        }

        println("$cfg")
        val tacProg = toTAC(cfg)
        println(dumpTAC(tacProg))
        Assertions.assertEquals(true, verify(tacProg))
    }

    @Test
    fun test2() {
        val cfg = SbfTestDSL.makeCFG("test2") {
            bb(0) {
                r1 = 3
                r2 = 2
                "CVT_nativeint_u64_mul"()
                r1 = r0
                r2 = 6
                "CVT_nativeint_u64_eq"()
                assert(CondOp.EQ(r0, 1))
                exit()
            }
        }

        println("$cfg")
        val tacProg = toTAC(cfg)
        println(dumpTAC(tacProg))
        Assertions.assertEquals(true, verify(tacProg))
    }

    @Test
    fun test3() {
        val cfg = SbfTestDSL.makeCFG("test3") {
            bb(0) {
                r1 = 3
                r2 = 2
                r3 = 4
                "CVT_nativeint_u64_muldiv"()
                r1 = r0
                r2 = 1
                "CVT_nativeint_u64_eq"()
                assert(CondOp.EQ(r0, 1))
                exit()
            }
        }

        println("$cfg")
        val tacProg = toTAC(cfg)
        println(dumpTAC(tacProg))
        Assertions.assertEquals(true, verify(tacProg))
    }

    @Test
    fun test4() {
        val cfg = SbfTestDSL.makeCFG("test4") {
            bb(0) {
                r1 = 3
                r2 = 2
                r3 = 4
                "CVT_nativeint_u64_muldiv_ceil"()
                r1 = r0
                r2 = 2
                "CVT_nativeint_u64_eq"()
                assert(CondOp.EQ(r0, 1))
                exit()
            }
        }

        println("$cfg")
        val tacProg = toTAC(cfg)
        println(dumpTAC(tacProg))
        Assertions.assertEquals(true, verify(tacProg))
    }

    @Test
    fun test5() {
        val cfg = SbfTestDSL.makeCFG("test5") {
            bb(0) {
                r1 = 29
                r2 = 10
                "CVT_nativeint_u64_sub"()
                r1 = r0
                r2 = 19
                "CVT_nativeint_u64_eq"()
                assert(CondOp.EQ(r0, 1))
                exit()
            }
        }

        println("$cfg")
        val tacProg = toTAC(cfg)
        println(dumpTAC(tacProg))
        Assertions.assertEquals(true, verify(tacProg))
    }

    @Test
    fun `sext(42, 32) == 42 returns positive value with sign bit 0 is unchanged`() {
        val cfg = SbfTestDSL.makeCFG("test") {
            bb(0) {
                r1 = 42
                r2 = 32
                "CVT_nativeint_u64_sext"()
                r1 = r0
                r2 = 42
                "CVT_nativeint_u64_eq"()
                assert(CondOp.EQ(r0, 1))
                exit()
            }
        }

        println("$cfg")
        val tacProg = toTAC(cfg)
        println(dumpTAC(tacProg))
        Assertions.assertEquals(true, verify(tacProg))
    }

    @Test
    fun `sext(0xFF, 8) == neg(1)`() {
        val cfg = SbfTestDSL.makeCFG("test") {
            bb(0) {
                r1 = 255  // 0xFF
                r2 = 8
                "CVT_nativeint_u64_sext"()
                r3 = r0   // save -1 (256-bit)
                r1 = 1
                "CVT_nativeint_u64_neg"()
                // r0 = neg(1) = -1 (256-bit)
                r2 = r0
                r1 = r3
                "CVT_nativeint_u64_eq"()
                assert(CondOp.EQ(r0, 1))
                exit()
            }
        }

        println("$cfg")
        val tacProg = toTAC(cfg)
        println(dumpTAC(tacProg))
        Assertions.assertEquals(true, verify(tacProg))
    }

    @Test
    fun `neg(0) == 0`() {
        val cfg = SbfTestDSL.makeCFG("test") {
            bb(0) {
                r1 = 0
                "CVT_nativeint_u64_neg"()
                r1 = r0
                r2 = 0
                "CVT_nativeint_u64_eq"()
                assert(CondOp.EQ(r0, 1))
                exit()
            }
        }

        println("$cfg")
        val tacProg = toTAC(cfg)
        println(dumpTAC(tacProg))
        Assertions.assertEquals(true, verify(tacProg))
    }

    @Test
    fun `neg(5) + 5 == 0`() {
        val cfg = SbfTestDSL.makeCFG("test") {
            bb(0) {
                r1 = 5
                "CVT_nativeint_u64_neg"()
                r1 = r0   // r1 = -5 (256-bit)
                r2 = 5
                "CVT_nativeint_u64_add"()
                r1 = r0
                r2 = 0
                "CVT_nativeint_u64_eq"()
                assert(CondOp.EQ(r0, 1))
                exit()
            }
        }

        println("$cfg")
        val tacProg = toTAC(cfg)
        println(dumpTAC(tacProg))
        Assertions.assertEquals(true, verify(tacProg))
    }

    @Test
    fun `sext(0x1_80000000, 32) slt 0`() {
        val cfg = SbfTestDSL.makeCFG("test") {
            bb(0) {
                r1 = 6442450944L  // 0x1_8000_0000, lower 32 bits = 0x8000_0000 = 2^31
                r2 = 32
                "CVT_nativeint_u64_sext"() // r0 = 2^256 - 2^31 =  0xFFFF...FFFF_8000_0000 (negative number)
                r1 = r0
                r2 = 0
                "CVT_nativeint_u64_slt"()
                assert(CondOp.EQ(r0, 1))
                exit()
            }
        }

        println("$cfg")
        val tacProg = toTAC(cfg)
        println(dumpTAC(tacProg))
        Assertions.assertEquals(true, verify(tacProg))
    }

    @Test
    fun `sext(0x1_80000000, 32) + 2^31 == 0`() {
        val cfg = SbfTestDSL.makeCFG("test") {
            bb(0) {
                r1 = 6442450944L  // 0x1_8000_0000, lower 32 bits = 0x8000_0000 = 2^31
                r2 = 32
                "CVT_nativeint_u64_sext"()  // r0 = 2^256 -2^31
                r1 = r0
                r2 = 2147483648L            // 2^31
                "CVT_nativeint_u64_add"()   // r0 = 2^256 -2^31 + 2^31 == 0 (wraparound)
                r1 = r0
                r2 = 0
                "CVT_nativeint_u64_eq"()
                assert(CondOp.EQ(r0, 1))
                exit()
            }
        }

        println("$cfg")
        val tacProg = toTAC(cfg)
        println(dumpTAC(tacProg))
        Assertions.assertEquals(true, verify(tacProg))
    }

    @Test
    fun `sext(-5 in 64-bit, 64) + 5 == 0`() {
        val cfg = SbfTestDSL.makeCFG("test") {
            bb(0) {
                r1 = -5L  // 0xFFFF_FFFF_FFFF_FFFB: negative in 64-bit (bit 63 set)
                r2 = 64
                "CVT_nativeint_u64_sext"()  // r0 = 0xFFFF...FFFF_FFFF_FFFF_FFFB = 2^256 - 5
                r1 = r0
                r2 = 5
                "CVT_nativeint_u64_add"()   // r0 = -5 + 5 == 0
                r1 = r0
                r2 = 0
                "CVT_nativeint_u64_eq"()
                assert(CondOp.EQ(r0, 1))
                exit()
            }
        }

        println("$cfg")
        val tacProg = toTAC(cfg)
        println(dumpTAC(tacProg))
        Assertions.assertEquals(true, verify(tacProg))
    }


    @Test
    fun `sext(-5 in 64-bit, 128) + 5 == 0`() {
        val cfg = SbfTestDSL.makeCFG("test") {
            bb(0) {
                r1 = -5L  // 0xFFFF_FFFF_FFFF_FFFB: negative in 64-bit
                r2 = 128
                "CVT_nativeint_u64_sext"()  // r0 = 0xFFFF...FFFF_FFFF_FFFF_FFFB = 2^256 - 5
                r1 = r0
                r2 = 5
                "CVT_nativeint_u64_add"()   // r0 = -5 + 5 == 0
                r1 = r0
                r2 = 0
                "CVT_nativeint_u64_eq"()
                assert(CondOp.EQ(r0, 1))
                exit()
            }
        }

        println("$cfg")
        val tacProg = toTAC(cfg)
        println(dumpTAC(tacProg))
        Assertions.assertEquals(true, verify(tacProg))
    }

    @Test
    fun `unsupported bitwidth should throw an exception`() {
        val cfg = SbfTestDSL.makeCFG("test") {
            bb(0) {
                r1 = 0L
                r2 = 15
                "CVT_nativeint_u64_sext"()
                exit()
            }
        }

        println("$cfg")
        expectException<TACTranslationError> {
            toTAC(cfg)
        }
    }
}
