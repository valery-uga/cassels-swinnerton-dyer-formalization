import AllCharacteristics.CubicSurfaceMain
import PfaffianDescent.VoisinDegreeElevenActualNativeEffectiveEightFactory

/-! The literal finite-extension equivalence from the paper's introduction.
The degree-ten geometry is supplied by the actual native residual factory;
only the global Coray alternative remains an external theorem hypothesis.
The result is stated for arbitrary homogeneous cubics, including singular and
zero forms, so the nonzero form in the paper needs no further restriction. -/

noncomputable section
namespace AllCharacteristics
open AlgebraicGeometry CategoryTheory MvPolynomial
open HomogeneousProjective PfaffianDescent

universe u

theorem twoProofs_finite_point_coprime_has_point_of_coray
    (coray : ∀ (K : Type u) [Field K] [CharZero K], CorayDegreeOneFourOrTenFor K)
    {k L : Type u} [Field k] [Field L] [Algebra k L] [Module.Finite k L]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    (hdegree : Nat.Coprime (Module.finrank k L) 3)
    (x : Fin 4 → L) (hx : x ≠ 0)
    (heval : p.eval₂ (algebraMap k L) x = 0) :
    ∃ y : Fin 4 → k, y ≠ 0 ∧ p.eval y = 0 :=
  cubic_coordinates_of_finite_point_coprime_of_voisin
    (fun K _ _ => voisinDegreeOneOrFourFor_of_coray_and_effectiveDegreeFour
      (coray K) voisinDegreeTenSelectedAvoidance_actualNative_effectiveDegreeFourFactory)
    p hp hdegree x hx heval

/-- `thm:main:intro`: representing zero nontrivially over the ground field
is equivalent to representing zero nontrivially over some finite extension
of degree coprime to three. The reverse witness is the original field itself. -/
theorem twoProofs_intro_finiteExtension_iff_of_coray
    (coray : ∀ (K : Type u) [Field K] [CharZero K], CorayDegreeOneFourOrTenFor K)
    {k : Type u} [Field k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) :
    (∃ y : Fin 4 → k, y ≠ 0 ∧ p.eval y = 0) ↔
    (∃ (L : Type u) (hL : Field L),
      letI := hL
      ∃ hAlg : Algebra k L,
        letI := hAlg
        ∃ _ : Module.Finite k L,
          Nat.Coprime (Module.finrank k L) 3 ∧
          ∃ x : Fin 4 → L, x ≠ 0 ∧ p.eval₂ (algebraMap k L) x = 0) := by
  constructor
  · rintro ⟨y, hy, hey⟩
    refine ⟨k, inferInstance, Algebra.id k, inferInstance, ?_, y, hy, ?_⟩
    · simp
    · simpa only [Algebra.algebraMap_self, MvPolynomial.eval₂_id] using hey
  · rintro ⟨L, hL, hAlg, hFinite, hdegree, x, hx, heval⟩
    letI := hL
    letI := hAlg
    letI := hFinite
    exact twoProofs_finite_point_coprime_has_point_of_coray
      coray p hp hdegree x hx heval

end AllCharacteristics
