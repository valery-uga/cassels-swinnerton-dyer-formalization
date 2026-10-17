import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Linear-algebra estimates in Voisin's section arguments

This file proves the rank estimates used twice in the degree-ten reduction.
They are independent of the later geometric assertions that the chosen
sections have zero-dimensional vanishing loci.
-/

namespace PfaffianDescent
open Module

section
variable {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- The kernel of a map has dimension at least the dimension of the source
minus the dimension of the target. -/
theorem finrank_sub_le_finrank_ker (f : V →ₗ[K] W) :
    finrank K V - finrank K W ≤ finrank K (LinearMap.ker f) := by
  have hrange := f.finrank_range_add_finrank_ker
  have hle : finrank K (LinearMap.range f) ≤ finrank K W :=
    Submodule.finrank_le _
  omega

/-- If the source has at least `d+r` dimensions and the target at most `d`,
then at least `r` independent source directions vanish. -/
theorem le_finrank_ker_of_target_bound (f : V →ₗ[K] W) (d r : ℕ)
    (hsource : d + r ≤ finrank K V) (htarget : finrank K W ≤ d) :
    r ≤ finrank K (LinearMap.ker f) := by
  have h := finrank_sub_le_finrank_ker f
  omega

/-- If the marked points impose independent conditions even after
restricting to sections containing a fixed curve, then the conditions
imposed by that curve lower the surviving section count by the same amount.
This is the linear-algebra step behind equation (35) of Voisin's Lemma 3.3.
The geometric assertion that generic points give the stated surjectivity is
kept explicit. -/
theorem fixedCurve_surviving_sections_bound
    {T : Type*} [AddCommGroup T] [Module K T] [FiniteDimensional K T]
    (evaluation : V →ₗ[K] W) (curveRestriction : V →ₗ[K] T)
    (d r c : ℕ)
    (htarget : finrank K W = d)
    (hsource : finrank K V ≤ d + r)
    (hcurve : finrank K (LinearMap.ker curveRestriction) + c ≤ finrank K V)
    (hgeneric : Function.Surjective
      (evaluation.domRestrict (LinearMap.ker curveRestriction))) :
    finrank K (LinearMap.ker
      (evaluation.domRestrict (LinearMap.ker curveRestriction))) + c ≤ r := by
  let restricted := evaluation.domRestrict (LinearMap.ker curveRestriction)
  have hrange : LinearMap.range restricted = ⊤ :=
    LinearMap.range_eq_top.mpr hgeneric
  have hdim := restricted.finrank_range_add_finrank_ker
  rw [hrange, finrank_top, htarget] at hdim
  dsimp only [restricted] at hdim
  omega

/-- The exact disjoint-curve estimate used in Voisin's Lemma 3.3: after
normalizing the test-point count, a curve imposing at least `l + 2`
conditions leaves fewer than `2s` sections through generic length-`d`
points. -/
theorem fixedCurve_surviving_sections_lt_two_mul
    {T : Type*} [AddCommGroup T] [Module K T] [FiniteDimensional K T]
    (evaluation : V →ₗ[K] W) (curveRestriction : V →ₗ[K] T)
    (d s l : ℕ)
    (htarget : finrank K W = d)
    (hsource : finrank K V ≤ d + (2 * s + 1))
    (hcurve : finrank K (LinearMap.ker curveRestriction) + (l + 2) ≤
      finrank K V)
    (hgeneric : Function.Surjective
      (evaluation.domRestrict (LinearMap.ker curveRestriction))) :
    finrank K (LinearMap.ker
      (evaluation.domRestrict (LinearMap.ker curveRestriction))) < 2 * s := by
  have h := fixedCurve_surviving_sections_bound
    evaluation curveRestriction d (2 * s + 1) (l + 2)
    htarget hsource hcurve hgeneric
  omega

/-- The same disjoint-curve estimate with the correct maximal-rank
genericity condition. If the curve-containing system has fewer than `d`
sections, generic evaluation is injective; otherwise it is surjective.
Either alternative leaves fewer than `2s` surviving sections. -/
theorem fixedCurve_surviving_sections_lt_two_mul_of_maximal_rank
    {T : Type*} [AddCommGroup T] [Module K T] [FiniteDimensional K T]
    (evaluation : V →ₗ[K] W) (curveRestriction : V →ₗ[K] T)
    (d s l : ℕ) (hs : 0 < s)
    (htarget : finrank K W = d)
    (hsource : finrank K V ≤ d + (2 * s + 1))
    (hcurve : finrank K (LinearMap.ker curveRestriction) + (l + 2) ≤
      finrank K V)
    (hgeneric : Function.Surjective
      (evaluation.domRestrict (LinearMap.ker curveRestriction)) ∨
      Function.Injective
      (evaluation.domRestrict (LinearMap.ker curveRestriction))) :
    finrank K (LinearMap.ker
      (evaluation.domRestrict (LinearMap.ker curveRestriction))) < 2 * s := by
  rcases hgeneric with hsurj | hinj
  · exact fixedCurve_surviving_sections_lt_two_mul
      evaluation curveRestriction d s l htarget hsource hcurve hsurj
  · have hker : LinearMap.ker
        (evaluation.domRestrict (LinearMap.ker curveRestriction)) = ⊥ :=
      LinearMap.ker_eq_bot.mpr hinj
    rw [hker, finrank_bot]
    omega

/-- Failure of surjectivity at marked points is witnessed by a nonzero
linear relation among their evaluation functionals.  Its projectivization
is the proper parameter space for the deficient-rank incidence locus in
Voisin's moving-curve argument. -/
theorem not_surjective_iff_exists_evaluation_relation
    (evaluation : V →ₗ[K] W) :
    ¬ Function.Surjective evaluation ↔
      ∃ φ : W →ₗ[K] K, φ ≠ 0 ∧ ∀ v, φ (evaluation v) = 0 := by
  constructor
  · intro hnot
    have hrange : LinearMap.range evaluation < ⊤ := by
      apply lt_top_iff_ne_top.mpr
      intro htop
      exact hnot (LinearMap.range_eq_top.mp htop)
    obtain ⟨φ, hφ, hker⟩ :=
      (LinearMap.range evaluation).exists_le_ker_of_lt_top hrange
    refine ⟨φ, hφ, ?_⟩
    intro v
    exact LinearMap.mem_ker.mp (hker ⟨v, rfl⟩)
  · rintro ⟨φ, hφ, hzero⟩ hsurj
    apply hφ
    ext y
    obtain ⟨v, rfl⟩ := hsurj y
    exact hzero v

/-- At eleven marked points, a system with at most fifteen sections has at
most four sections left in the evaluation kernel whenever evaluation has
maximal rank. -/
theorem eleven_point_maximal_rank_kernel_finrank_le_four
    (evaluation : V →ₗ[K] W)
    (hsource : finrank K V ≤ 15)
    (htarget : finrank K W = 11)
    (hmax : Function.Surjective evaluation ∨
      Function.Injective evaluation) :
    finrank K (LinearMap.ker evaluation) ≤ 4 := by
  rcases hmax with hsurj | hinj
  · have hrange : LinearMap.range evaluation = ⊤ :=
      LinearMap.range_eq_top.mpr hsurj
    have hdim := evaluation.finrank_range_add_finrank_ker
    rw [hrange, finrank_top, htarget] at hdim
    omega
  · have hker : LinearMap.ker evaluation = ⊥ :=
      LinearMap.ker_eq_bot.mpr hinj
    rw [hker, finrank_bot]
    decide

/-- A twelve-dimensional system has at most one section vanishing at eleven
points whenever the evaluation map has maximal rank. -/
theorem eleven_point_maximal_rank_kernel_finrank_le_one
    (evaluation : V →ₗ[K] W)
    (hsource : finrank K V ≤ 12)
    (htarget : finrank K W = 11)
    (hmax : Function.Surjective evaluation ∨
      Function.Injective evaluation) :
    finrank K (LinearMap.ker evaluation) ≤ 1 := by
  rcases hmax with hsurj | hinj
  · have hrange : LinearMap.range evaluation = ⊤ :=
      LinearMap.range_eq_top.mpr hsurj
    have hdim := evaluation.finrank_range_add_finrank_ker
    rw [hrange, finrank_top, htarget] at hdim
    omega
  · have hker : LinearMap.ker evaluation = ⊥ :=
      LinearMap.ker_eq_bot.mpr hinj
    rw [hker, finrank_bot]
    decide

/-- Two multiplication systems of dimensions at most ten and four, sharing
a nonzero cubic, span at most thirteen dimensions. If a nonzero defining
cubic in that span vanishes after projection to the surface coordinate
ring, their projected span has dimension at most twelve. This is the
linear-algebra count for cubics containing a plane conic. -/
theorem two_cubic_systems_projected_finrank_le_twelve
    {A B H Q : Type*}
    [AddCommGroup A] [Module K A] [FiniteDimensional K A]
    [AddCommGroup B] [Module K B] [FiniteDimensional K B]
    [AddCommGroup H] [Module K H] [FiniteDimensional K H]
    [AddCommGroup Q] [Module K Q]
    (f : A →ₗ[K] H) (g : B →ₗ[K] H) (π : H →ₗ[K] Q)
    (hA : finrank K A ≤ 10) (hB : finrank K B ≤ 4)
    (common : ∃ h : H, h ≠ 0 ∧
      h ∈ LinearMap.range f ∧ h ∈ LinearMap.range g)
    (killed : ∃ h : H, h ≠ 0 ∧
      h ∈ LinearMap.range f ⊔ LinearMap.range g ∧ π h = 0) :
    finrank K ((LinearMap.range f ⊔ LinearMap.range g).map π) ≤ 12 := by
  let Rf : Submodule K H := LinearMap.range f
  let Rg : Submodule K H := LinearMap.range g
  let S : Submodule K H := Rf ⊔ Rg
  have hU : finrank K Rf ≤ 10 := (LinearMap.finrank_range_le f).trans hA
  have hV : finrank K Rg ≤ 4 := (LinearMap.finrank_range_le g).trans hB
  obtain ⟨h, hne, hUmem, hVmem⟩ := common
  have hinf : 0 < finrank K ↥(Rf ⊓ Rg) := by
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    exact ⟨⟨h, ⟨hUmem, hVmem⟩⟩, fun hz => hne (congrArg Subtype.val hz)⟩
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq Rf Rg
  have hS : finrank K S ≤ 13 := by
    dsimp only [S]
    omega
  let restricted := π.domRestrict S
  obtain ⟨p, hpne, hpS, hπp⟩ := killed
  have hker : 0 < finrank K (LinearMap.ker restricted) := by
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    refine ⟨⟨⟨p, hpS⟩, LinearMap.mem_ker.mpr hπp⟩, ?_⟩
    intro hz
    exact hpne (congrArg Subtype.val (congrArg Subtype.val hz))
  have hdim := restricted.finrank_range_add_finrank_ker
  have hrange : LinearMap.range restricted = S.map π :=
    LinearMap.range_domRestrict S π
  rw [hrange] at hdim
  change finrank K ↥(S.map π) + finrank K ↥(LinearMap.ker restricted) =
    finrank K S at hdim
  change finrank K ↥(S.map π) ≤ 12
  omega

/-- A strict source/target dimension inequality produces a nonzero vector in
the kernel. -/
theorem exists_ne_zero_mem_ker_of_finrank_lt (f : V →ₗ[K] W)
    (h : finrank K W < finrank K V) :
    ∃ v : V, v ≠ 0 ∧ f v = 0 := by
  have hk : 0 < finrank K (LinearMap.ker f) := by
    have := finrank_sub_le_finrank_ker f
    omega
  have : Nontrivial (LinearMap.ker f) := Module.finrank_pos_iff.mp hk
  obtain ⟨v, hv⟩ := exists_ne (0 : LinearMap.ker f)
  exact ⟨v.val, by
    intro hz
    apply hv
    apply Subtype.ext
    exact hz, v.property⟩

set_option linter.unusedSectionVars false in
/-- Conversely, a surjective map with a nonzero kernel has target dimension
strictly smaller than source dimension.  This is the dimension-count form
used when generic points impose independent conditions but a nonzero section
still vanishes at all of them. -/
theorem finrank_lt_of_surjective_of_exists_ne_zero_mem_ker
    (f : V →ₗ[K] W) (hsurj : Function.Surjective f)
    (hker : ∃ v : V, v ≠ 0 ∧ f v = 0) :
    finrank K W < finrank K V := by
  obtain ⟨v, hv, hfv⟩ := hker
  have hkerpos : 0 < finrank K (LinearMap.ker f) := by
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    refine ⟨⟨v, LinearMap.mem_ker.mpr hfv⟩, ?_⟩
    intro hz
    apply hv
    exact congrArg Subtype.val hz
  have hrange : LinearMap.range f = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have hdim := f.finrank_range_add_finrank_ker
  rw [hrange, finrank_top] at hdim
  omega

/-- If evaluation at `d` marked points is surjective and a nonzero section
vanishes at all of them, the section space has dimension at least `d + 1`.
This is the exact linear-algebra content of Voisin's generic-point estimate
`h⁰ ≥ d + 1`. -/
theorem succ_le_finrank_of_surjective_evaluation_with_nonzero_kernel
    (d : ℕ) (ev : V →ₗ[K] (Fin d → K))
    (hsurj : Function.Surjective ev)
    (hker : ∃ v : V, v ≠ 0 ∧ ev v = 0) :
    d + 1 ≤ finrank K V := by
  have hlt :=
    finrank_lt_of_surjective_of_exists_ne_zero_mem_ker ev hsurj hker
  have htarget : finrank K (Fin d → K) = d := by
    rw [Module.finrank_pi_fintype]
    simp
  rw [htarget] at hlt
  omega

/-- If evaluation leaves at least two dimensions in its kernel, two linearly
independent sections vanish simultaneously.  This is the linear pencil used
in Voisin's rank-two construction before the separate geometric argument
proves that its members have zero-dimensional zero schemes. -/
theorem exists_linearIndependent_pair_mem_ker_of_finrank_target_lt
    (f : V →ₗ[K] W) (h : finrank K W + 1 < finrank K V) :
    ∃ v : Fin 2 → V, LinearIndependent K v ∧ ∀ i, f (v i) = 0 := by
  have hker : 2 ≤ finrank K (LinearMap.ker f) := by
    have hbound := finrank_sub_le_finrank_ker f
    omega
  have hkerpos : 0 < finrank K (LinearMap.ker f) := by omega
  letI : Nontrivial (LinearMap.ker f) := Module.finrank_pos_iff.mp hkerpos
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : LinearMap.ker f)
  have hsingle : LinearIndependent K (![v₀] : Fin 1 → LinearMap.ker f) :=
    LinearIndependent.of_subsingleton 0 hv₀
  obtain ⟨v₁, hv⟩ := exists_linearIndependent_snoc_of_lt_finrank hsingle
    (by omega : 1 < finrank K (LinearMap.ker f))
  let w : Fin 2 → LinearMap.ker f := Fin.snoc (![v₀]) v₁
  refine ⟨fun i ↦ (w i).1, ?_, ?_⟩
  · change LinearIndependent K ((LinearMap.ker f).subtype ∘ w)
    simpa [w] using
      hv.map' (LinearMap.ker f).subtype (Submodule.ker_subtype (LinearMap.ker f))
  · intro i
    exact LinearMap.mem_ker.mp (w i).property

end

section RankTwo
variable {K E : Type*} [Field K]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- Evaluation of rank-two sections at `s` rational geometric points has
target dimension `2s`. -/
theorem rankTwo_evaluation_target_finrank (s : ℕ) :
    finrank K (Fin s → Fin 2 → K) = 2 * s := by
  rw [Module.finrank_pi_fintype]
  simp [Nat.mul_comm]

/-- More than `2s` sections force a nonzero section vanishing at all `s`
rank-two fibers.  This is the exact linear estimate used in Proposition 3.2.
-/
theorem exists_rankTwo_section_vanishing
    (s : ℕ) (ev : E →ₗ[K] (Fin s → Fin 2 → K))
    (hsections : 2 * s < finrank K E) :
    ∃ e : E, e ≠ 0 ∧ ev e = 0 := by
  apply exists_ne_zero_mem_ker_of_finrank_lt ev
  rw [rankTwo_evaluation_target_finrank]
  exact hsections

end RankTwo
end PfaffianDescent
