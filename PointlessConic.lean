import Mathlib.Tactic

/- A proof that x^2 + y^2 = 3 has no rational solutions -/

/-
First, a proof that x^2 + y^2 = 3 has no integer solutions.
The idea is that this equation has no solutions mod 4,
so there cannot be any integer solutions.
-/

-- A description of the square classes mod 4: z^2 = 0 mod 4 or z^2 = 1 mod 4.
lemma mod4squares : ∀ z : ℤ, z^2 % 4 = 0 ∨ z^2 % 4 = 1 := by
    -- intro z as a variable to use in the proof
    intro z

    -- split into cases: either z is even or odd
    rcases Int.even_or_odd z with (heven | hodd)

    -- if z is even
    · unfold Even at heven -- use the definition of even
      rcases heven with ⟨k, hk⟩ -- use k as a witness for the definition
      rw [hk]
      ring_nf -- simplify (k+k)^2 = 4*k^2
      left
      apply Int.mul_emod_left (k^2) 4

    -- if z is odd
    · unfold Odd at hodd
      rcases hodd with ⟨k, hk⟩ -- use k as a witness for the definition
      rw [hk]
      ring_nf -- simplify (2*k+1)^2 = 1 + 4*k + 4*k^2
      right
      rw[add_assoc, Int.add_emod 1 (k*4+k^2*4) 4, Int.add_emod (k*4) (k^2*4) 4]
      rw[Int.mul_emod_left k 4, Int.mul_emod_left (k^2) 4]
      rw[add_zero,Int.zero_emod,add_zero]
      rfl


-- If an integer squares to 0 mod 4, then it is even.
lemma zerosqmod4 (n : ℤ) : n^2 % 4 = 0 → (Even n) := by
  contrapose!
  rw[Int.not_even_iff_odd]
  intro h
  unfold Odd at h
  rcases h with ⟨k, hk⟩
  rw [hk]
  ring_nf
  rw[add_assoc, Int.add_emod 1 (k*4+k^2*4) 4, Int.add_emod (k*4) (k^2*4) 4]
  rw[Int.mul_emod_left k 4, Int.mul_emod_left (k^2) 4]
  trivial


-- There are no integer solutions to x^2 + y^2 = 3.
theorem nointegersolutions : ¬∃(x y : ℤ), x^2 + y^2 = 3 := by
  intro h
  rcases h with ⟨x, y, heq⟩

  -- reduce equation mod 4
  have hmod4 : (x^2 + y^2) % 4 = 3 % 4 := by
    rw [heq]

  -- (x^2+y^2)% 4 = x^2 %4 + y^2 %4
  rw[Int.add_emod (x^2) (y^2) 4] at hmod4

  -- derive contradiction from possible square residues
  rcases mod4squares x with (hx0 | hx1)
  -- x = 0 mod 4
  · rcases mod4squares y with (hy0 | hy1)
    · rw [hx0, hy0] at hmod4
      trivial
    · rw [hx0, hy1] at hmod4
      trivial

  -- x = 1 mod 4
  · rcases mod4squares y with (hy0 | hy1)
    · rw [hx1, hy0] at hmod4
      trivial
    · rw [hx1, hy1] at hmod4
      trivial


/-
The proof that there are no rational solutions to x^2 + y^2 = 3
requires that we show that there are no rational numbers squaring to 3
to cover the cases where, say, x = 0.
-/

lemma sqrt3irrational : ¬∃(x:ℚ), x^2 = 3 := by
  by_contra h
  rcases h with ⟨x , hx⟩

  -- √3 is irrational as the square root of a prime number
  have irrsqrt : Irrational √3 := by
    apply Nat.Prime.irrational_sqrt
    exact Nat.prime_three

  -- consider square roots of both sides of x^2 = 3
  have sqr : √(x^2) = √3 := by
    refine Eq.symm ((fun {x y} hx hy ↦ (Real.sqrt_eq_iff_mul_self_eq hx hy).mpr) ?_ ?_ ?_)
    · linarith
    · rw[Real.sqrt_sq_eq_abs (x:ℝ)]
      apply IsAbsoluteValue.abv_nonneg
    · ring_nf
      rw[Real.sqrt_sq_eq_abs (x:ℝ)]
      rw[sq_abs]
      norm_cast
      apply Eq.symm hx

  -- x = ± √3
  have pmcases : x = √3 ∨ x = -√3 := by
    rw[Real.sqrt_sq_eq_abs] at sqr
    norm_cast at sqr
    refine mul_self_eq_mul_self_iff.mp ?_
    ring_nf
    simp
    norm_cast

  -- but √3 is irrational
  have xirr : Irrational x := by
    rcases pmcases with hpos | hneg
    · rw [hpos]
      exact irrsqrt
    · rw [hneg]
      exact Irrational.neg irrsqrt

  apply Rat.not_irrational x
  exact xirr


/-
To prove nonexistence of rational solutions, we prove that there are no
~integer~ solutions to the equation x^2 + y^2 = 3z^2
(obtained by clearing denominators).

To do this, we again consider residue classes mod 4.

A key difference is that there is now a solution mod 4
(with x, y, and z all reducing to zero).

We rule out this case using a descent argument, which we formalize with
the following inductive steps.
-/


-- Setup for the strong induction step
theorem strongind (n : ℕ) : ∀(x : ℕ) (_ : x < n), ¬∃(y z: ℤ) (_ : y≠ 0) (_: z≠0), x^2 + y^2 = 3*z^2
:= by

  induction n -- induct on n

  case zero => -- if n is zero, then the statement vacuously holds
    intro x hx h
    trivial

  case succ n hn => -- if n ≥ 0, show that n+1 case holds
    intro x hx h
    -- hx : x < n+1
    rcases hx with _ | hx -- either x = n or x < n

    -- suppose x = n
    · rcases h with ⟨y, z, yne, hz⟩
      rcases hz with ⟨zne, h⟩

      -- reduce equation mod 4
      have hmod4 : (n^2 + y^2) % 4 = (3 * z^2) % 4 := by
        rw [h]

      rw[Int.add_emod (n^2) (y^2) 4] at hmod4
      rw[Int.mul_emod 3 (z^2) 4] at hmod4


      -- derive contradiction from cases of possible square residues
      rcases mod4squares n with (hn0 | hn1)
      · rcases mod4squares y with (hy0 | hy1)
        · rcases mod4squares z with (hz0 | hz1)
          -- this is the interesting case: what if all of n,y,z are 0 mod 4? -> descent
          · have neven : Even (n:ℤ) := by
              apply zerosqmod4
              exact hn0
            have yeven : Even y := by
              apply zerosqmod4
              exact hy0
            have zeven : Even z := by
              apply zerosqmod4
              exact hz0

            -- use even to write n = 2k, y = 2l, z = 2m
            rcases neven with ⟨k, hk⟩
            rcases yeven with ⟨l, hl⟩
            rcases zeven with ⟨m, hm⟩

            have lne0 : l ≠ 0 := by
              rw [hl] at yne
              exact Ne.symm (ne_of_apply_ne (fun l ↦ l + l) fun a ↦ yne (id (Eq.symm a)))

            have mne0 : m ≠ 0 := by
              rw [hm] at zne
              exact Ne.symm (ne_of_apply_ne (fun m ↦ m + m) fun a ↦ zne (id (Eq.symm a)))

            -- rewrite h in terms of k,l,m, then divide the equation by 4
            have oneside : n^2+y^2-3*z^2 = 0 := by
              exact Int.sub_eq_zero.mpr h

            rw [hk, hl, hm] at oneside
            ring_nf at oneside

            have hred : 4*(k^2+l^2-3*m^2) = 0 := by
              ring_nf
              exact oneside

            have hdiv : (k^2+l^2-3*m^2) = 0 := by
              apply mul_eq_zero.1 at hred
              rcases hred with htriv | hexact -- 4 = 0 or k^2 + l^2 - 3*m^2 = 0
              · trivial -- 4 ≠ 0
              exact hexact

            have hdesired : k^2 + l^2 = 3*m^2 := by
              exact Int.eq_of_sub_eq_zero hdiv

            have ngeq0 : n ≥ 0 := by
              exact Nat.zero_le n

            have ncases : n > 0 ∨ n = 0 := by
              exact Or.symm (Nat.eq_zero_or_pos n)

            rcases ncases with hnge0 | neq0
            -- if n > 0, then k < n and we can use the induction hypothesis
            · have hnge0coe : (n : ℤ) > 0 := by
                exact Int.natCast_pos.mpr hnge0

              have kge0 : k > 0 := by
                rw [hk] at hnge0coe
                exact pos_add_self_iff.mp hnge0coe

              have coe : (Int.toNat k) = k := by
                refine Int.toNat_of_nonneg ?_
                exact Int.le_of_lt kge0

              have klen : k < n := by
                rw [hk]
                linarith

              have knatlen : (Int.toNat k) < n:= by
                exact (Int.toNat_lt' hnge0).mpr klen

              apply hn (Int.toNat k)
              · use knatlen -- Int.toNat k < n
              use l
              use m
              use lne0
              use mne0
              rw [coe]
              exact hdesired

            -- if n = 0, contradict that the square root of three is irrational
            rw [neq0] at h
            ring_nf at h

            have ratcoe : (y:ℚ)^2 = (z:ℚ)^2 * 3 := by
              -- rw [← Rat.cast_mul (z^2) 3]
              rw [← Rat.intCast_inj, Rat.intCast_mul] at h
              repeat rw [Rat.intCast_pow] at h
              exact h


            have z2coene0 : (z:ℚ)^2 ≠ 0 := by
              exact pow_ne_zero 2 (Rat.num_ne_zero.mp zne)

            have frac2 : ((y:ℚ) / (z:ℚ))^2 = 3 := by
              rw [div_pow]
              exact Eq.symm (CancelDenoms.cancel_factors_eq_div (id (Eq.symm ratcoe)) z2coene0)

            apply sqrt3irrational
            use y/z

          · rw [hn0, hy0, hz1] at hmod4
            trivial
        · rcases mod4squares z with (hz0 | hz1)
          · rw [hn0, hy1, hz0] at hmod4
            trivial
          · rw [hn0, hy1, hz1] at hmod4
            trivial

      · rcases mod4squares y with (hy0 | hy1)
        · rcases mod4squares z with (hz0 | hz1)
          · rw [hn1, hy0, hz0] at hmod4
            trivial
          · rw [hn1, hy0, hz1] at hmod4
            trivial
        · rcases mod4squares z with (hz0 | hz1)
          · rw [hn1, hy1, hz0] at hmod4
            trivial
          · rw [hn1, hy1, hz1] at hmod4
            trivial

    -- if x < n, done by inductive hypothesis.
    · exact hn x hx h

-- The strong induction step indeed implies that the following statement holds for all n
theorem nointsolnsinduction (x : ℕ) (_ : x ≠ 0) : ¬∃(y z: ℤ) (_ : y≠ 0) (_: z≠0), x^2 + y^2 = 3*z^2
:= by
  apply strongind (x+1)
  linarith

-- A proof of the desired form from the induction statement:
theorem nointegersolutions2 : ¬∃(x y z: ℤ) (_: x ≠ 0) (_ : y≠ 0) (_: z≠0), x^2 + y^2 = 3*z^2 := by
  intro h
  rcases h with ⟨x, y, z, xnz, ynz, znz, heq⟩

  -- x, a nonzero integer is nonnegative or negative
  rcases x with x | x

  -- if x = m (nonneg) natural number, then it is zero or equal to succ a
  · rcases x with zero | x
    -- if x = 0, then the hypotheses are not met
    · trivial
    -- if x > 0, then should be able to apply nointsolnsind
    · have xnzcoe : (x + 1 ≠ 0) := by
        exact fun a ↦ xnz (congrArg Int.ofNat a)
      apply nointsolnsinduction (x+1) xnzcoe
      use y
      use z
      use ynz
      use znz
      exact heq


  -- if x < 0, ...
  · rw[Int.negSucc_eq] at *

    have xnzposcoe : (x+1 ≠ 0) := by
      exact Ne.symm (Nat.zero_ne_add_one x)

    have heq2 : Int.ofNat (x + 1) ^ 2 + y ^ 2 = 3 * z ^ 2 := by
      exact heq

    apply nointsolnsinduction (x+1) xnzposcoe
    use y
    use z
    use ynz
    use znz
    exact heq

-- Translating the nonexistence of integer solutions to the desired statement:
theorem norationalsolutions : ¬∃(x y : ℚ), x^2 + y^2 = (3: ℚ) := by
  intro h
  rcases h with ⟨x, y, heq⟩

  -- witness x and y as quotients of integers in lowest terms

  -- gather useful variables (maybe in a more easily accessible way than with rcases)
  let a := x.num
  let b := x.den
  let c := y.num
  let d := y.den

  -- show that a, b, c, and d are nonzero
  have aneq0 : a≠ 0:= by
    by_contra h
    unfold a at h
    rw [Rat.zero_of_num_zero h] at heq
    rw [zero_pow, zero_add] at heq
    · apply sqrt3irrational
      use y
    · trivial -- proves that 2 ≠ 0 in order to use zero_pow

  have bneq0 : b ≠ 0 := Rat.den_ne_zero x

  have cneq0 : c ≠ 0 := by
    by_contra h
    unfold c at h
    rw [Rat.zero_of_num_zero h] at heq
    rw [zero_pow, add_zero] at heq
    · apply sqrt3irrational
      use x
    · trivial -- proves that 2 ≠ 0 in order to use zero_pow

  have dneq0 : d ≠ 0 := Rat.den_ne_zero y

  -- witness x as a quotient of a and b (coerced to be rational numbers)
  have hx : x = a/b := by
    exact Eq.symm (Rat.num_div_den x)

  -- same for y with c and d
  have hy : y = c/d := by
    exact Eq.symm (Rat.num_div_den y)

  -- rewrite heq in terms of a, b, c, and d (computations treating a,b,c,d as rationals for now)
  have heq2 : (a:ℚ)^2/(b:ℚ)^2 + (c:ℚ)^2/(d:ℚ)^2 = (3:ℚ) := by
    rw [hx, hy] at heq
    repeat rw [div_pow] at heq
    exact heq

  -- multiply both sides by b^2 * d^2
  have heq3: ((a:ℚ)^2/(b:ℚ)^2 + (c:ℚ)^2/(d:ℚ)^2 ) * (↑b ^ 2 * ↑d ^ 2) = 3 * (b ^ 2 * d ^ 2) := by
    apply Mathlib.Tactic.LinearCombination.mul_eq_const heq2 (b^2* d^2)

  -- to clear denominators, need to ensure that b^2, d^2 ≠ 0
  have b2neq0: (b:ℚ)^2 ≠ 0 := by
    norm_cast
    exact pow_ne_zero 2 bneq0

  have d2neq0: (d:ℚ)^2 ≠ 0 := by
    norm_cast
    exact pow_ne_zero 2 dneq0

  -- clear denominators
  have heq4 : ((a:ℚ)^2 * (d:ℚ)^2 + (c:ℚ)^2 * (b:ℚ)^2) = 3 * ((b:ℚ)^2 * (d:ℚ)^2) := by
    ring_nf at heq3
    simp at heq3
    nth_rewrite 2 [mul_assoc] at heq3
    rw[Rat.mul_inv_cancel (↑b ^ 2)] at heq3
    · rw[mul_one] at heq3 -- cancelling b^2 requires b^2 ≠ 0
      nth_rewrite 1 [mul_assoc] at heq3
      rw[Rat.mul_inv_cancel (↑d ^ 2)] at heq3
      · rw[mul_one] at heq3 -- cancelling d^2 requires d^2 ≠ 0
        nth_rewrite 2 [mul_comm] at heq3
        nth_rewrite 3 [mul_comm] at heq3
        exact heq3
      -- d^2 ≠ 0
      exact d2neq0
    -- b^2 ≠ 0
    exact b2neq0

  -- rewrite equation in terms of integers
  have heq5 : (a*d)^2 + (c*b)^2 = 3 * (b*d)^2 := by
    ring_nf
    ring_nf at heq4
    norm_cast at heq4

  let l := a*d
  let m := c*b
  let n := (b*d:ℤ)

  have hcontra : l^2 + m^2 = 3 * n^2 := by
    exact heq5

  -- verify that each of l, m, and n are nonzero to apply "nointegersolutions2"
  have lneq0 : l ≠ 0 := by
    intro h
    unfold l at h
    rw [mul_eq_zero] at h
    rcases h with ha | hd
    · apply aneq0
      exact ha
    · apply dneq0
      norm_cast at hd

  have mneq0 : m ≠ 0 := by
    intro h
    unfold m at h
    rw [mul_eq_zero] at h
    rcases h with hc | hb
    · apply cneq0
      exact hc
    · apply bneq0
      norm_cast at hb

  have nneq0 : n ≠ 0 := by
    intro h
    unfold n at h
    rw [mul_eq_zero] at h
    rcases h with hb | hd
    · apply bneq0
      norm_cast at hb
    · apply dneq0
      norm_cast at hd

  apply nointegersolutions2
  use l
  use m
  use n
