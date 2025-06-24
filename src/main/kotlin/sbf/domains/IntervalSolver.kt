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

package sbf.domains

import datastructures.stdcollections.*
import sbf.cfg.CondOp

interface Interval<I> {
    /** return true if this is the empty interval **/
    fun isEmpty(): Boolean
    /** return true if this is the largest interval **/
    fun isTop(): Boolean
    /** Refine this with [cst] **/
    fun filter(cst: SbfIntervalConstraint): I
}

/** If lb > ub then the interval is interpreted as the "empty" interval **/
data class UnsignedInterval(val lb: ULong, val ub: ULong): Interval<UnsignedInterval> {
    private fun lessThan(other: UnsignedInterval) = ub < other.lb
    private fun overlap(other: UnsignedInterval) = !lessThan(other) && !other.lessThan(this)
    private fun intersection(other: UnsignedInterval): UnsignedInterval {
        return if (!this.overlap(other)) {
            mkEmpty()
        } else {
            val lower = kotlin.math.max(lb, other.lb)
            val upper = kotlin.math.min(ub, other.ub)
            UnsignedInterval(lower, upper)
        }
    }

    companion object {

        private fun toULong(n: ExpressionNum): ULong {
            // Even if n.n is a `BigInteger` we should not have constants that cannot be represented using
            // 64 bits. If that's the case then `toLong`() truncates to 64 bits.
            return n.n.toLong().toULong()
        }

        fun mkTop() = UnsignedInterval(0UL, ULong.MAX_VALUE)
        fun mkEmpty() = UnsignedInterval(1UL, 0UL)
        fun from(cst: SbfIntervalConstraint): UnsignedInterval {
            val k = toULong(cst.n)
            return when (cst.op) {
                CondOp.EQ -> UnsignedInterval(k, k)
                CondOp.NE -> {
                    when (k) {
                        0UL -> UnsignedInterval(1UL, ULong.MAX_VALUE)
                        ULong.MAX_VALUE -> UnsignedInterval(0UL, ULong.MAX_VALUE-1UL)
                        else -> mkTop()
                    }
                }
                // Unsigned comparisons
                CondOp.LE -> UnsignedInterval(0UL, k)
                CondOp.GE -> UnsignedInterval(k, ULong.MAX_VALUE)
                CondOp.LT -> {
                    if (k == 0UL) {
                        mkEmpty()
                    } else {
                        UnsignedInterval(0UL, k - 1UL)
                    }
                }
                CondOp.GT -> {
                    if (k ==  ULong.MAX_VALUE) {
                        mkEmpty()
                    } else {
                        UnsignedInterval(k + 1UL, ULong.MAX_VALUE)
                    }
                }
                // Signed comparisons
                CondOp.SLE, CondOp.SGE, CondOp.SLT, CondOp.SGT -> mkTop()
            }
        }
    }


    override fun isEmpty() = lb > ub
    override fun isTop() = lb == 0UL && ub == ULong.MAX_VALUE
    override fun filter(cst: SbfIntervalConstraint): UnsignedInterval {
        return when (cst.op) {
            CondOp.NE -> {
                val k = toULong(cst.n)
                if (lb == k) {
                    UnsignedInterval(lb+1UL, ub)
                } else if (ub == k) {
                    UnsignedInterval(lb, ub-1UL)
                } else {
                    this
                }
            }
            else -> {
                this.intersection(from(cst))
            }
        }
    }
}



interface IntervalFactory<I> {
    fun mkTop(): I
}

class UnsignedIntervalFactory: IntervalFactory<UnsignedInterval> {
    override fun mkTop() = UnsignedInterval.mkTop()
}

/**
 * Solver for interval constraints.
 *
 * [csts] is interpreted as the conjunction of each [SbfIntervalConstraint].
 **/
class IntervalSolver<I: Interval<I>>(val csts: Set<SbfIntervalConstraint>, val fac: IntervalFactory<I>) {

    /**
     * Constructor that takes a list of arbitrary linear constraints.
     *
     * **Important note**: this constructor simply filters out any linear constraint that is not an interval constraint.
     * Even, trivial contradictions (0 > 1) will be removed by this constructor.
     */
    constructor(cs: List<SbfLinearConstraint>, fac: IntervalFactory<I>): this(
        cs.filter { SbfIntervalConstraint.isIntervalConstraint(it)}
            .map { SbfIntervalConstraint(it) }
            .toSet(),
        fac
    )

    /**
     * Return null iff there is not a solution to the set of interval constraints.
     * Otherwise, it returns a map from variables to intervals.
     **/
    fun run(): Map<ExpressionVar, I>? {
        val sol = mutableMapOf<ExpressionVar, I>()
        for (c in csts) {
            val v = c.v
            val oldIntv = sol.getOrDefault(v, fac.mkTop())
            val refinedIntv = oldIntv.filter(c)
            if (refinedIntv.isEmpty()) {
                return null
            } else {
                sol[v] = refinedIntv
            }
        }
        return sol
    }
}
