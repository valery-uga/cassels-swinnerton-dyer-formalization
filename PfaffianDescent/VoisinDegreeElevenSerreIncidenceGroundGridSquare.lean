import PfaffianDescent.VoisinDegreeElevenSerreIncidenceGroundGridOpen

/-! # Literal coefficient-extension square of the selected ground-grid point -/
noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem serreIncidenceGroundGridSpec_coefficient_square
    {K E : Type u} [Field K] [Field E] [Algebra K E]
    {σ : Type u} (x : σ → K) :
    Spec.map (CommRingCat.ofHom
        (MvPolynomial.eval (fun i => algebraMap K E (x i)))) ≫
      Spec.map (CommRingCat.ofHom (MvPolynomial.map (algebraMap K E))) =
    Spec.map (CommRingCat.ofHom (algebraMap K E)) ≫
      Spec.map (CommRingCat.ofHom (MvPolynomial.eval x)) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro p
  change MvPolynomial.eval (fun i => algebraMap K E (x i))
      (MvPolynomial.map (algebraMap K E) p) = algebraMap K E (MvPolynomial.eval x p)
  rw [MvPolynomial.eval_map]
  exact (MvPolynomial.eval₂_comp (algebraMap K E) x p).symm

theorem serreIncidenceAffineOpen_exists_ground_section_square
    {K E : Type u} [Field K] [Field E] [Algebra K E] [Infinite K]
    {σ : Type u} (U : (Spec (.of (MvPolynomial σ E))).Opens)
    (hU : (U : Set (Spec (.of (MvPolynomial σ E)))).Nonempty) :
    ∃ (x : σ → K) (q : Spec (.of E) ⟶ (U : Scheme.{u})),
      q ≫ U.ι = Spec.map (CommRingCat.ofHom
        (MvPolynomial.eval (fun i => algebraMap K E (x i)))) ∧
      q ≫ U.ι ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.map (algebraMap K E))) =
        Spec.map (CommRingCat.ofHom (algebraMap K E)) ≫
          Spec.map (CommRingCat.ofHom (MvPolynomial.eval x)) := by
  obtain ⟨x,q,hq⟩ := serreIncidenceAffineOpen_exists_ground_grid (K := K) U hU
  refine ⟨x,q,hq,?_⟩
  rw [← Category.assoc, hq]
  exact serreIncidenceGroundGridSpec_coefficient_square x

end PfaffianDescent
