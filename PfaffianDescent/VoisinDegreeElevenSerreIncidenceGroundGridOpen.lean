import PfaffianDescent.VoisinDegreeElevenSerreIncidenceGroundGridAvoidance
import AllCharacteristics.UnirationalityCycle

/-! # A genuine nonempty affine open contains a point of the ground-field grid -/
noncomputable section
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem serreIncidenceAffineOpen_exists_ground_grid
    {K E : Type u} [Field K] [Field E] [Algebra K E] [Infinite K]
    {σ : Type u} (U : (Spec (.of (MvPolynomial σ E))).Opens)
    (hU : (U : Set (Spec (.of (MvPolynomial σ E)))).Nonempty) :
    ∃ (x : σ → K) (q : Spec (.of E) ⟶ (U : Scheme.{u})),
      q ≫ U.ι = Spec.map (CommRingCat.ofHom
        (MvPolynomial.eval (fun i => algebraMap K E (x i)))) := by
  obtain ⟨y, hy⟩ := hU
  obtain ⟨f, hfU, hyf⟩ :=
    (isAffineOpen_top (Spec (.of (MvPolynomial σ E)))).exists_basicOpen_le
      (V := U) ⟨y, hy⟩ trivial
  let p : MvPolynomial σ E := (Scheme.ΓSpecIso (.of (MvPolynomial σ E))).hom f
  have hp : p ≠ 0 := by
    intro hp
    have hf : f = 0 := by
      have h := congrArg (fun z => (Scheme.ΓSpecIso (.of (MvPolynomial σ E))).inv z) hp
      simpa [p] using h
    subst hf
    simp at hyf
  obtain ⟨x, hx⟩ := serreIncidencePolynomial_exists_ground_nonzero (K := K) p hp
  have hUp : (Spec (.of (MvPolynomial σ E))).basicOpen
      ((Scheme.ΓSpecIso (.of (MvPolynomial σ E))).inv p) ≤ U := by
    simpa [p] using hfU
  obtain ⟨q, hq⟩ := exists_rational_point_of_spec_basicOpen_le U p hUp
    (MvPolynomial.eval (fun i => algebraMap K E (x i))) hx
  exact ⟨x, q, hq⟩

end PfaffianDescent
