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

import config.ConfigScope
import sbf.cfg.*
import sbf.testing.SbfTestDSL
import org.junit.jupiter.api.*

class TACU128Test {

    /** 128-bits unsigned ceil division **/
    @Test
    fun test1() {
        val cfg = SbfTestDSL.makeCFG("test1") {
            bb(0) {
                r1 = r10
                BinOp.SUB(r1, 104)
                r2 = 3
                r3 = 0
                r4 = 2
                r5 = 0
                "CVT_u128_ceil_div"()
                r2 = r1[0]
                r3 = r1[8]
                assert(CondOp.EQ(r2, 2UL))
                assert(CondOp.EQ(r3, 0UL))
                exit()
            }
        }


        ConfigScope(SolanaConfig.UseTACMathInt, true).use {
            println("$cfg")
            val tacProg = toTAC(cfg)
            println(dumpTAC(tacProg))
            Assertions.assertEquals(true, verify(tacProg))
        }
    }

    /** 128-bits unsigned floor division **/
    @Test
    fun test2() {
        val cfg = SbfTestDSL.makeCFG("test2") {
            bb(0) {
                r1 = r10
                BinOp.SUB(r1, 104)
                r2 = 3
                r3 = 0
                r4 = 2
                r5 = 0
                "__udivti3"()
                r2 = r1[0]
                r3 = r1[8]
                assert(CondOp.EQ(r2, 1UL))
                assert(CondOp.EQ(r3, 0UL))
                exit()
            }
        }


        ConfigScope(SolanaConfig.UseTACMathInt, true).use {
            println("$cfg")
            val tacProg = toTAC(cfg)
            println(dumpTAC(tacProg))
            Assertions.assertEquals(true, verify(tacProg))
        }
    }

    /** 128-bits less or equal **/
    @Test
    fun test3() {
        val cfg = SbfTestDSL.makeCFG("test3") {
            bb(0) {
                r1 = 10
                r2 = 0
                r3 = 20
                r4 = 0
                "CVT_u128_leq"()
                assert(CondOp.EQ(r0, 1UL))
                exit()
            }
        }


        ConfigScope(SolanaConfig.UseTACMathInt, true).use {
            println("$cfg")
            val tacProg = toTAC(cfg)
            println(dumpTAC(tacProg))
            Assertions.assertEquals(true, verify(tacProg))
        }
    }

    /** 128-bits less or equal **/
    @Test
    fun test4() {
        val cfg = SbfTestDSL.makeCFG("test4") {
            bb(0) {
                r1 = 10
                r2 = 1
                r3 = 20
                r4 = 0
                "CVT_u128_leq"()
                assert(CondOp.EQ(r0, 0UL))
                exit()
            }
        }


        ConfigScope(SolanaConfig.UseTACMathInt, true).use {
            println("$cfg")
            val tacProg = toTAC(cfg)
            println(dumpTAC(tacProg))
            Assertions.assertEquals(true, verify(tacProg))
        }
    }

    /** 128-bits less or equal: high(x)==0, high(y)!=0 → true **/
    @Test
    fun `u128 leq returns true when high(x) is zero and high(y) is non-zero`() {
        val cfg = SbfTestDSL.makeCFG("u128 leq returns true when high(x) is zero and high(y) is non-zero") {
            bb(0) {
                r1 = 10
                r2 = 0
                r3 = 5
                r4 = 1
                "CVT_u128_leq"()
                assert(CondOp.EQ(r0, 1UL))
                exit()
            }
        }

        ConfigScope(SolanaConfig.UseTACMathInt, true).use {
            println("$cfg")
            val tacProg = toTAC(cfg)
            println(dumpTAC(tacProg))
            Assertions.assertEquals(true, verify(tacProg))
        }
    }

    /** 128-bits less or equal: both highs non-zero, x > y → false **/
    @Test
    fun `u128 leq returns false when both highs are non-zero and x is greater than y`() {
        val cfg = SbfTestDSL.makeCFG("u128 leq returns false when both highs are non-zero and x is greater than y") {
            bb(0) {
                r1 = 5
                r2 = 1
                r3 = 20
                r4 = 0
                "CVT_u128_leq"()
                assert(CondOp.EQ(r0, 0UL))
                exit()
            }
        }

        ConfigScope(SolanaConfig.UseTACMathInt, true).use {
            println("$cfg")
            val tacProg = toTAC(cfg)
            println(dumpTAC(tacProg))
            Assertions.assertEquals(true, verify(tacProg))
        }
    }

    /** 128-bits less or equal: x == y → true **/
    @Test
    fun `u128 leq returns true when x equals y`() {
        val cfg = SbfTestDSL.makeCFG("u128 leq returns true when x equals y") {
            bb(0) {
                r1 = 10
                r2 = 0
                r3 = 10
                r4 = 0
                "CVT_u128_leq"()
                assert(CondOp.EQ(r0, 1UL))
                exit()
            }
        }

        ConfigScope(SolanaConfig.UseTACMathInt, true).use {
            println("$cfg")
            val tacProg = toTAC(cfg)
            println(dumpTAC(tacProg))
            Assertions.assertEquals(true, verify(tacProg))
        }
    }

    /** 128-bits greater than zero: x == 0 → false **/
    @Test
    fun `u128 gt0 returns false when x is zero`() {
        val cfg = SbfTestDSL.makeCFG("u128 gt0 returns false when x is zero") {
            bb(0) {
                r1 = 0
                r2 = 0
                "CVT_u128_gt0"()
                assert(CondOp.EQ(r0, 0UL))
                exit()
            }
        }

        ConfigScope(SolanaConfig.UseTACMathInt, true).use {
            println("$cfg")
            val tacProg = toTAC(cfg)
            println(dumpTAC(tacProg))
            Assertions.assertEquals(true, verify(tacProg))
        }
    }

    /** 128-bits greater than zero: low != 0, high == 0 → true **/
    @Test
    fun `u128 gt0 returns true when low is non-zero and high is zero`() {
        val cfg = SbfTestDSL.makeCFG("u128 gt0 returns true when low is non-zero and high is zero") {
            bb(0) {
                r1 = 5
                r2 = 0
                "CVT_u128_gt0"()
                assert(CondOp.EQ(r0, 1UL))
                exit()
            }
        }

        ConfigScope(SolanaConfig.UseTACMathInt, true).use {
            println("$cfg")
            val tacProg = toTAC(cfg)
            println(dumpTAC(tacProg))
            Assertions.assertEquals(true, verify(tacProg))
        }
    }

    /** 128-bits greater than zero: low == 0, high != 0 → true **/
    @Test
    fun `u128 gt0 returns true when low is zero and high is non-zero`() {
        val cfg = SbfTestDSL.makeCFG("u128 gt0 returns true when low is zero and high is non-zero") {
            bb(0) {
                r1 = 0
                r2 = 1
                "CVT_u128_gt0"()
                assert(CondOp.EQ(r0, 1UL))
                exit()
            }
        }

        ConfigScope(SolanaConfig.UseTACMathInt, true).use {
            println("$cfg")
            val tacProg = toTAC(cfg)
            println(dumpTAC(tacProg))
            Assertions.assertEquals(true, verify(tacProg))
        }
    }

}
