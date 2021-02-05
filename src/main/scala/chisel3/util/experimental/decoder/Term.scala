package chisel3.util.experimental.decoder

/** Term: boolean expression that can express bit in a bit vector to be assert, not asserted and don't care.
  *
  * @param value Literal bits, 1 -> 1, 0 -> 0, ? -> 0
  * @param mask  Mask bits, 1 -> 0, 0 -> 0, ? -> 1
  * @example Suppose `F(a, b, c, d)` is a boolean function with four inputs.
  *          Then `Term(01?1)` represents `F(0, 1, ?, 1)` which in turn represents `F(0, 1, 0, 1) and F(0, 1, 1, 1)`.
  */
private class Term(val value: BigInt, val mask: BigInt = 0) {
  // I think this requirement should be satisfied, which also is a good self-explanation to user(delete this before upstreaming)
  require((value & mask) == 0, "bit 1 should not be masked.")

  /** a `var` indicate whether this term is a [[https://en.wikipedia.org/wiki/Implicant#Prime_implicant]]. */
  var prime = true

  /** Rule to define coverage relationship among `0`, `1` and `?`:
    *   1. '?' covers '0' and '1', '0' covers '0', '1' covers '1'
    *   1. '1' doesn't cover '?', '1' doesn't cover '0'
    *   1. '0' doesn't cover '?', '0' doesn't cover '1'
    *
    * [[covers]] means all bits in `this` cover the correspond position in `x`.
    *
    * // below documentation should rework. docs in [[intersects]] did a good job.(delete this before upstreaming)
    * {{{
    * value ^^ x.value                                       // different
    * (value ^^ x.value) &~ mask                             // different and I care
    * (value ^^ x.value) &~ mask | x.mask                    // (different and valid) or the other term don't care
    * ((value ^^ x.value) &~ mask | x.mask) &~ mask          // ->
    * ((value ^^ x.value) &~ mask &~ mask) | (x.mask &~ mask)// ->
    * ((value ^^ x.value) &~ mask) | (x.mask &~ mask)        // (different and I care) or (the other term don't care but I care)
    * (((value ^^ x.value) &~ mask | x.mask) &~ mask) == 0   // no such bits that are ((different and I care) or (the other term doesn't care but I care))
    *                                                        // all bits are (not (different and I care) and not (the other term doesn't care but I care))
    *                                                        // all bits are (not different or I don't care) and not (the other term doesn't care but I care))
    *                                                        //          the same -> covers | either 0 or 1 is fine for me -> covers
    *                                                        //                                                  not (the other term needs this bit to be fine
    *                                                        //                                                  with either 0 or 1, but I can only tolerant one value)
    * }}}
    *
    * @example {{{
    * this       // = ?0?1
    * this.value // = 0001
    * this.mask  // = 1010
    *
    * x          // = 10??
    * x.value    // = 1000
    * x.mask     // = 0011
    *
    * value ^^ x.value                                       // ->  1001
    * (value ^^ x.value) &~ mask                             // ->  0001
    * (value ^^ x.value) &~ mask | x.mask                    // ->  0011
    * (value ^^ x.value) &~ mask | x.mask &~ mask            // ->  0001 (not covered because `1` doesn't cover `?`)
    * }}}
    * @example {{{
    * this       // = 10??
    * this.value // = 1000
    * this.mask  // = 0011
    *
    * x          // = 10?1
    * x.value    // = 1001
    * x.mask     // = 0010
    *
    * value ^^ x.value                                       // -> 0001
    * (value ^^ x.value) &~ mask                             // -> 0000
    * (value ^^ x.value) &~ mask | x.mask                    // -> 0010
    * (value ^^ x.value) &~ mask | x.mask &~ mask            // -> 0000 (covered)
    * }}}
    * @param x to check is covered by `this` or not.
    * @return Whether `this` covers `x`
    */
  def covers(x: Term): Boolean = ((value ^ x.value) &~ mask | x.mask &~ mask).signum == 0

  /** Check whether two terms have the same value on all of the cared bits (intersection).
    *
    * {{{
    * value ^^ x.value                                       // bits that are different
    * (bits that are different) &~ mask                      // bits that are different and `this` care
    * (bits that are different and `this` care) &~ x.mask    // bits that are different and `both` care
    * (bits that are different and both care).signum == 0    // (bits that are different and we both care) == 0
    * (bits that are different and both care) == 0           // no (bits that are different and we both care) exists
    * no (bits that are different and we both care) exists   // all cared bits are the same, two terms intersect
    * }}}
    *
    * @param x Term to be checked with
    * @return Whether two terms intersect
    */
  def intersects(x: Term): Boolean = ((value ^ x.value) &~ mask &~ x.mask).signum == 0

  /** Two terms equal only when both of their values and masks are the same.
    *
    * @param that Term to be checked with
    * @return Whether two terms are equal
    */
  override def equals(that: Any): Boolean = that match {
    case x: Term => x.value == value && x.mask == mask
    case _ => false
  }

  // I think hashCode not containing mask is not good. (delete this before upstreaming)
  override def hashCode: Int = value.toInt

  /** "Smaller" comparator
    * If two terms have different value, then their order is determined by the value, or by the mask.
    *
    * @param that Term to be compared with
    * @return Whether this term is smaller than the other
    */
  def <(that: Term): Boolean = value < that.value || value == that.value && mask < that.mask

  /** Check whether two terms are similar.
    * Two terms are "similar" when they satisfy all the following rules:
    *   1. have the same mask ('?'s are at the same positions)
    *   1. values only differ by one bit
    *   1. the bit at the differed position of this term is '1' (that of the other term is '0')
    *
    * @example this = 11?0, x = 10?0 -> similar
    * @example this = 11??, x = 10?0 -> not similar, violated rule 1
    * @example this = 11?1, x = 10?0 -> not similar, violated rule 2
    * @example this = 10?0, x = 11?0 -> not similar, violated rule 3
    * @param x Term to be checked with
    * @return Whether this term is similar to the other
    */
  def similar(x: Term): Boolean = {
    val diff = value - x.value
    mask == x.mask && value > x.value && (diff & diff - 1) == 0
  }

  /** Merge two similar terms (when simplifying)
    * Rule of merging: '0' and '1' merge to '?'
    *
    * @param x Term to be merged with
    * @return A new term representing the merge result
    */
  def merge(x: Term): Term = {
    require(similar(x), s"merge is only reasonable when $this similar $x")

    // if two term can be merged, then they both are not prime implicants.
    prime = false
    x.prime = false
    val bit = value - x.value
    new Term(value &~ bit, mask | bit)
  }

  override def toString: String = value.toString(16) + "-" + mask.toString(16) + (if (prime) "p" else "")
}
