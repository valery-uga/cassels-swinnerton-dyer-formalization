import AllCharacteristics.CharacteristicZeroDegreeOneReduction
import AllCharacteristics.ArbitraryFieldCubicPointDescent
import AllCharacteristics.ArbitraryFieldCubicCycleDescent
import AllCharacteristics.SchemeQuadraticDescent
import AllCharacteristics.SchemeCubicDescent
import PfaffianDescent.VoisinCycleArithmetic
import PfaffianDescent.HomogeneousDimensions

/-!
# External degree reduction and the smooth Cassels--Swinnerton-Dyer theorem

This file records exactly the external input from Voisin used by the paper.
Coray's theorem is background, while Ma's lifting method has already been
formalized in the imported characteristic-zero reduction.  No external result
is introduced as an axiom: the input is an explicit hypothesis of the final
theorems.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
open HomogeneousProjective
open PfaffianDescent
universe u

/- The elementary section-count used in Voisin's application is the
dimension of quadrics in four projective variables.  The identification with
the degree-two line-bundle sections on the cubic surface is geometric input;
the monomial count itself is internal. -/
theorem cubic_quadratic_polynomial_section_finrank
    {k : Type u} [Field k] :
    Module.finrank k (MvPolynomial.homogeneousSubmodule (Fin 4) k 2) = 10 := by
  rw [four_variable_homogeneous_finrank]
  decide

/-- Voisin's characteristic-zero reduction over a fixed field, stated using
the actual closed points and zero-cycles of the projective hypersurface. -/
def VoisinDegreeOneOrFourFor (k : Type u) [Field k] [CharZero k] : Prop :=
  ∀ (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3),
    p ≠ 0 → Smooth (hypersurfaceToBase p hp) →
    ∀ z : ZeroCycle (hypersurface p hp),
      ZeroCycle.degree (hypersurfaceToBase p hp) z = 1 →
      ∃ x : closedPoints (hypersurface p hp),
        (hypersurfaceToBase p hp).residueDegree x.1 = 1 ∨
        (hypersurfaceToBase p hp).residueDegree x.1 = 4

/- A uniform strengthening of the quadratic effectivity output used in the
paper's `4 ↔ 5` argument.  The degree-three reference cycle is supplied
explicitly; the geometric content (choosing a disjoint line section and
applying Voisin's Lemma 3.6) is isolated in this proposition rather than
hidden in a degree-reduction theorem. -/
def VoisinQuadraticEffectivityFor (k : Type u) [Field k] [CharZero k] : Prop :=
  ∀ (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3),
    p ≠ 0 → Smooth (hypersurfaceToBase p hp) →
    ∀ h : EffectiveZeroCycle (hypersurface p hp),
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp) h = 3 →
      ∀ z : EffectiveZeroCycle (hypersurface p hp),
        EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 4 ∨
          EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 5 →
        CurveFamilyCycleQuotient.IsEffective (hypersurfaceToBase p hp)
          (3 • curveFamilyCycleClass (hypersurfaceToBase p hp) h.toZeroCycle -
            curveFamilyCycleClass (hypersurfaceToBase p hp) z.toZeroCycle)

/- A concrete family-level form of the same uniform input.  Its endpoint
equation is the residual construction from a length `degree z + 3` subscheme
and four copies of the supplied degree-three reference cycle. -/
def VoisinQuadraticFamilyEffectivityFor (k : Type u) [Field k] [CharZero k] : Prop :=
  ∀ (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3),
    p ≠ 0 → Smooth (hypersurfaceToBase p hp) →
    ∀ h : EffectiveZeroCycle (hypersurface p hp),
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp) h = 3 →
      ∀ z : EffectiveZeroCycle (hypersurface p hp),
        EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 4 ∨
          EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 5 →
        ∃ F : RationalCycleFamily (hypersurfaceToBase p hp),
          ∃ r : EffectiveZeroCycle (hypersurface p hp),
            F.fiberCycle false = z + h + r ∧
            F.fiberCycle true = 4 • h

/-- The endpoint equalities in the quadratic family determine the residual
degree: it is `9 - degree z`, hence five for a degree-four input and four for
a degree-five input. -/
theorem voisinQuadraticFamily_residual_degree
    {k : Type u} [Field k] [CharZero k]
    (families : VoisinQuadraticFamilyEffectivityFor k)
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (h : EffectiveZeroCycle (hypersurface p hp))
    (hh : EffectiveZeroCycle.degree (hypersurfaceToBase p hp) h = 3)
    (z : EffectiveZeroCycle (hypersurface p hp))
    (hz : EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 4 ∨
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 5) :
    ∃ F : RationalCycleFamily (hypersurfaceToBase p hp),
      ∃ r : EffectiveZeroCycle (hypersurface p hp),
        F.fiberCycle false = z + h + r ∧ F.fiberCycle true = 4 • h ∧
          EffectiveZeroCycle.degree (hypersurfaceToBase p hp) r =
            9 - EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z := by
  obtain ⟨F, r, hzero, hinfinity⟩ := families p hp hne inferInstance h hh z hz
  refine ⟨F, r, hzero, hinfinity, ?_⟩
  have hd := F.fiberCycle_degree_eq
  rw [hzero, hinfinity, effectiveCycle_degree_add, effectiveCycle_degree_add,
    effectiveCycle_degree_nsmul, hh] at hd
  rcases hz with hz | hz
  · rw [hz] at hd
    norm_num at hd ⊢
    omega
  · rw [hz] at hd
    norm_num at hd ⊢
    omega

theorem voisinQuadraticEffectivityFor_of_familyEffectivityFor
    {k : Type u} [Field k] [CharZero k]
    (families : VoisinQuadraticFamilyEffectivityFor k) :
    VoisinQuadraticEffectivityFor k := by
  intro p hp hne hs h hh z hz
  obtain ⟨F, r, hzero, hinfinity⟩ := families p hp hne hs h hh z hz
  obtain ⟨r, hclass⟩ := residualClass_effective_of_rationalCycleFamily
    F (z + h) r h 4 (by simpa [add_assoc] using hzero) hinfinity
  refine ⟨r, ?_⟩
  have hclass' := hclass
  rw [effectiveCycleToSigned_add, map_add] at hclass'
  calc
    curveFamilyCycleClass (hypersurfaceToBase p hp) r.toZeroCycle =
        4 • curveFamilyCycleClass (hypersurfaceToBase p hp) h.toZeroCycle -
          (curveFamilyCycleClass (hypersurfaceToBase p hp) z.toZeroCycle +
            curveFamilyCycleClass (hypersurfaceToBase p hp) h.toZeroCycle) := hclass'
    _ = 3 • curveFamilyCycleClass (hypersurfaceToBase p hp) h.toZeroCycle -
          curveFamilyCycleClass (hypersurfaceToBase p hp) z.toZeroCycle := by
      simp only [succ_nsmul]
      abel

theorem effective_degree_four_of_voisin_quadratic_effectivity
    {k : Type u} [Field k] [CharZero k]
    (effectivity : VoisinQuadraticEffectivityFor k)
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (z : EffectiveZeroCycle (hypersurface p hp))
    (hz : EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 5) :
    ∃ r : EffectiveZeroCycle (hypersurface p hp),
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp) r = 4 := by
  obtain ⟨h, hh⟩ := hypersurface_exists_effective_degree_three
    (k := k) (n := 4) 0 1 (by decide) p hp
  exact PfaffianDescent.exists_effective_degree_four_of_quadratic_effectivity
    (hypersurfaceToBase p hp) h z hh hz (effectivity p hp hne inferInstance h hh z (Or.inr hz))

theorem effective_degree_five_of_voisin_quadratic_effectivity
    {k : Type u} [Field k] [CharZero k]
    (effectivity : VoisinQuadraticEffectivityFor k)
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (z : EffectiveZeroCycle (hypersurface p hp))
    (hz : EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 4) :
    ∃ r : EffectiveZeroCycle (hypersurface p hp),
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp) r = 5 := by
  obtain ⟨h, hh⟩ := hypersurface_exists_effective_degree_three
    (k := k) (n := 4) 0 1 (by decide) p hp
  exact PfaffianDescent.exists_effective_degree_five_of_quadratic_effectivity
    (hypersurfaceToBase p hp) h z hh hz (effectivity p hp hne inferInstance h hh z (Or.inl hz))

/-- The concrete endpoint-family version of the degree-five bridge.  The
family formulation is converted internally to the quotient effectivity
certificate before applying the residual-degree calculation. -/
theorem effective_degree_five_of_voisin_quadratic_family_effectivity
    {k : Type u} [Field k] [CharZero k]
    (families : VoisinQuadraticFamilyEffectivityFor k)
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (z : EffectiveZeroCycle (hypersurface p hp))
    (hz : EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 4) :
    ∃ r : EffectiveZeroCycle (hypersurface p hp),
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp) r = 5 := by
  exact effective_degree_five_of_voisin_quadratic_effectivity
    (voisinQuadraticEffectivityFor_of_familyEffectivityFor families)
    p hp hne z hz

/-- The companion degree-four residual obtained directly from the same
endpoint-family construction when the input cycle has degree five. -/
theorem effective_degree_four_of_voisin_quadratic_family_effectivity
    {k : Type u} [Field k] [CharZero k]
    (families : VoisinQuadraticFamilyEffectivityFor k)
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (z : EffectiveZeroCycle (hypersurface p hp))
    (hz : EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 5) :
    ∃ r : EffectiveZeroCycle (hypersurface p hp),
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp) r = 4 := by
  exact effective_degree_four_of_voisin_quadratic_effectivity
    (voisinQuadraticEffectivityFor_of_familyEffectivityFor families)
    p hp hne z hz

/-- Voisin's quadratic effectivity certificate gives the paper's effective
degree equivalence in both directions. -/
theorem effective_degree_four_iff_five_of_voisin_quadratic_effectivity
    {k : Type u} [Field k] [CharZero k]
    (effectivity : VoisinQuadraticEffectivityFor k)
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] :
    (∃ z : EffectiveZeroCycle (hypersurface p hp),
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 4) ↔
    (∃ z : EffectiveZeroCycle (hypersurface p hp),
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 5) := by
  constructor
  · rintro ⟨z, hz⟩
    exact effective_degree_five_of_voisin_quadratic_effectivity
      effectivity p hp hne z hz
  · rintro ⟨z, hz⟩
    exact effective_degree_four_of_voisin_quadratic_effectivity
      effectivity p hp hne z hz

/-- The same `4 ↔ 5` equivalence with Voisin's endpoint families supplied
directly. -/
theorem effective_degree_four_iff_five_of_voisin_quadratic_family_effectivity
    {k : Type u} [Field k] [CharZero k]
    (families : VoisinQuadraticFamilyEffectivityFor k)
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] :
    (∃ z : EffectiveZeroCycle (hypersurface p hp),
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 4) ↔
    (∃ z : EffectiveZeroCycle (hypersurface p hp),
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 5) :=
  effective_degree_four_iff_five_of_voisin_quadratic_effectivity
    (voisinQuadraticEffectivityFor_of_familyEffectivityFor families)
    p hp hne

/-- The paper's characteristic-zero `1/4` conclusion becomes a rational
section once Voisin's quadratic effectivity output is supplied: the degree-one
branch is immediate, while the degree-four branch is converted to degree five
and fed to the Pfaffian descent. -/
theorem smooth_cubic_section_of_voisin_and_quadratic_effectivity
    {k : Type u} [Field k] [CharZero k]
    (voisin : VoisinDegreeOneOrFourFor k)
    (effectivity : VoisinQuadraticEffectivityFor k)
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (z : ZeroCycle (hypersurface p hp))
    (hz : ZeroCycle.degree (hypersurfaceToBase p hp) z = 1) :
    ∃ s : Spec (.of k) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _ := by
  obtain ⟨x, hx₁ | hx₄⟩ := voisin p hp hne inferInstance z hz
  · exact section_of_residueDegree_one (hypersurfaceToBase p hp) x.1 hx₁
  · let z₄ : EffectiveZeroCycle (hypersurface p hp) := Finsupp.single x 1
    have hz₄ : EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z₄ = 4 := by
      simp [z₄, EffectiveZeroCycle.degree, hx₄]
    obtain ⟨z₅, hz₅⟩ := effective_degree_five_of_voisin_quadratic_effectivity
      effectivity p hp hne z₄ hz₄
    exact hypersurface_section_of_effective_degree_five p hp z₅ hz₅

/- The already formalized arbitrary-field cycle descent discharges the
   degree-four branch directly.  This records the resulting stronger
   characteristic-zero interface, so the quadratic-effectivity input is not
   needed for the rational-section conclusion. -/
theorem smooth_cubic_section_of_voisin_direct
    {k : Type u} [Field k] [CharZero k]
    (voisin : VoisinDegreeOneOrFourFor k)
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (z : ZeroCycle (hypersurface p hp))
    (hz : ZeroCycle.degree (hypersurfaceToBase p hp) z = 1) :
    ∃ s : Spec (.of k) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _ := by
  obtain ⟨x, hx₁ | hx₄⟩ := voisin p hp hne inferInstance z hz
  · exact section_of_residueDegree_one (hypersurfaceToBase p hp) x.1 hx₁
  · let z₄ : EffectiveZeroCycle (hypersurface p hp) := Finsupp.single x 1
    have hz₄ : EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z₄ = 4 := by
      simp [z₄, EffectiveZeroCycle.degree, hx₄]
    exact cubic_section_of_effective_degree_four_or_five p hp hne z₄ (Or.inl hz₄)

/-- The characteristic-zero smooth conclusion with Voisin's quadratic input
given directly as the finite-flat endpoint-family construction. -/
theorem smooth_cubic_section_of_voisin_and_quadratic_family_effectivity
    {k : Type u} [Field k] [CharZero k]
    (voisin : VoisinDegreeOneOrFourFor k)
    (families : VoisinQuadraticFamilyEffectivityFor k)
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (z : ZeroCycle (hypersurface p hp))
    (hz : ZeroCycle.degree (hypersurfaceToBase p hp) z = 1) :
    ∃ s : Spec (.of k) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _ := by
  obtain ⟨x, hx₁ | hx₄⟩ := voisin p hp hne inferInstance z hz
  · exact section_of_residueDegree_one (hypersurfaceToBase p hp) x.1 hx₁
  · let z₄ : EffectiveZeroCycle (hypersurface p hp) := Finsupp.single x 1
    have hz₄ : EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z₄ = 4 := by
      simp [z₄, EffectiveZeroCycle.degree, hx₄]
    obtain ⟨z₅, hz₅⟩ := effective_degree_five_of_voisin_quadratic_family_effectivity
      families p hp hne z₄ hz₄
    exact hypersurface_section_of_effective_degree_five p hp z₅ hz₅

theorem charZero_smooth_cubic_coordinates_of_voisin_and_quadratic_effectivity
    {k : Type u} [Field k] [CharZero k]
    (voisin : VoisinDegreeOneOrFourFor k)
    (effectivity : VoisinQuadraticEffectivityFor k)
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (z : ZeroCycle (hypersurface p hp))
    (hz : ZeroCycle.degree (hypersurfaceToBase p hp) z = 1) :
    ∃ y : Fin 4 → k, y ≠ 0 ∧ p.eval y = 0 := by
  obtain ⟨s, hs⟩ := smooth_cubic_section_of_voisin_and_quadratic_effectivity
    voisin effectivity p hp hne z hz
  exact (hypersurface_has_point_iff_coordinates (RingHom.id k) p hp).mp
    ⟨s, by simpa using hs⟩

/-- Voisin's reduction, together with the already formalized degree-four
descent, proves the characteristic-zero smooth case in coordinates. -/
theorem charZero_smooth_cubic_coordinates_of_voisin
    {k : Type u} [Field k] [CharZero k]
    (voisin : VoisinDegreeOneOrFourFor k)
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (z : ZeroCycle (hypersurface p hp))
    (hz : ZeroCycle.degree (hypersurfaceToBase p hp) z = 1) :
    ∃ y : Fin 4 → k, y ≠ 0 ∧ p.eval y = 0 := by
  obtain ⟨x, hx | hx⟩ := voisin p hp hne inferInstance z hz
  · obtain ⟨a, ha⟩ := hypersurface_section_of_closedPoint_degree_le_two
      p hp x (by omega)
    exact hypersurface_coordinates_of_point (RingHom.id k) p hp a (by simpa using ha)
  · obtain ⟨a, ha⟩ := cubic_section_of_closedPoint_degree_four_or_five
      p hp hne x (Or.inl hx)
    exact hypersurface_coordinates_of_point (RingHom.id k) p hp a (by simpa using ha)

/-- The constructed characteristic-changing reduction transports the
characteristic-zero conclusion back to every field. -/
theorem smooth_cubic_coordinates_of_zeroCycle_degree_one_of_voisin
    (voisin : ∀ (K : Type u) [Field K] [CharZero K], VoisinDegreeOneOrFourFor K)
    {k : Type u} [Field k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (z : ZeroCycle (hypersurface p hp))
    (hz : ZeroCycle.degree (hypersurfaceToBase p hp) z = 1) :
    ∃ y : Fin 4 → k, y ≠ 0 ∧ p.eval y = 0 := by
  obtain ⟨K, _, _, q, hq, hqne, hs, ⟨w, hw⟩, hspecialize⟩ :=
    exists_charZero_smooth_cubic_degree_one_reduction p hp hne z hz
  let _ : Smooth (hypersurfaceToBase q hq) := hs
  exact hspecialize
    (charZero_smooth_cubic_coordinates_of_voisin (voisin K) q hq hqne w hw)

/-- Scheme-theoretic form of the smooth case of the main theorem. -/
theorem smooth_cubic_section_of_zeroCycle_degree_one_of_voisin
    (voisin : ∀ (K : Type u) [Field K] [CharZero K], VoisinDegreeOneOrFourFor K)
    {k : Type u} [Field k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (z : ZeroCycle (hypersurface p hp))
    (hz : ZeroCycle.degree (hypersurfaceToBase p hp) z = 1) :
    ∃ a : Spec (.of k) ⟶ hypersurface p hp,
      a ≫ hypersurfaceToBase p hp = 𝟙 _ := by
  obtain ⟨y, hy, he⟩ :=
    smooth_cubic_coordinates_of_zeroCycle_degree_one_of_voisin voisin p hp hne z hz
  obtain ⟨a, ha⟩ := hypersurface_point_of_coordinates (RingHom.id k) p hp y hy he
  exact ⟨a, by simpa using ha⟩

/-- Equivalent finite-extension formulation in the smooth case: a point over
an extension of degree prime to three descends to the ground field. -/
theorem smooth_cubic_coordinates_of_finite_point_coprime_of_voisin
    (voisin : ∀ (K : Type u) [Field K] [CharZero K], VoisinDegreeOneOrFourFor K)
    {k L : Type u} [Field k] [Field L] [Algebra k L] [Module.Finite k L]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (hdegree : Nat.Coprime (Module.finrank k L) 3)
    (x : Fin 4 → L) (hx : x ≠ 0)
    (heval : p.eval₂ (algebraMap k L) x = 0) :
    ∃ y : Fin 4 → k, y ≠ 0 ∧ p.eval y = 0 := by
  obtain ⟨a, ha⟩ := hypersurface_point_of_coordinates (algebraMap k L) p hp x hx heval
  obtain ⟨z, hz⟩ := exists_effectiveZeroCycle_of_finite_algebra_point
    (hypersurfaceToBase p hp) a ha
  have hcoprime : Nat.Coprime
      (EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z) 3 := by
    rw [hz]
    exact hdegree
  obtain ⟨w, hw⟩ := cubicSurface_zeroCycle_degree_one_of_effective_coprime p hp z hcoprime
  exact smooth_cubic_coordinates_of_zeroCycle_degree_one_of_voisin
    voisin p hp hne w hw

end AllCharacteristics
