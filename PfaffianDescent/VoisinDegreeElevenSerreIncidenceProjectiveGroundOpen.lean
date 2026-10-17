import PfaffianDescent.VoisinDegreeElevenSerreIncidenceProjectiveGroundPoint

/-! # Ground points meet actual geometric opens of projective section space -/
noncomputable section
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem serreIncidenceProjectiveOpen_exists_ground_parameter
    {K E : Type u} [Field K] [Field E] [Algebra K E] [Infinite K]
    {σ : Type} [Finite σ]
    (U : (scheme (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ E))).Opens)
    (hU : (U : Set (scheme (⊥ : HomogeneousIdeal
      (MvPolynomial.homogeneousSubmodule σ E)))).Nonempty) :
    ∃ (qK : Spec (.of K) ⟶ scheme (⊥ : HomogeneousIdeal
        (MvPolynomial.homogeneousSubmodule σ K)))
      (qE : Spec (.of E) ⟶ (U : Scheme.{u})),
      qK ≫ toBase (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K)) = 𝟙 _ ∧
      qE ≫ U.ι ≫ toBase (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ E)) = 𝟙 _ ∧
      qE ≫ U.ι ≫ projectiveCoefficientMap (algebraMap K E)
        (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K))
        (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ E)) (by simp) =
      Spec.map (CommRingCat.ofHom (algebraMap K E)) ≫ qK := by
  obtain ⟨x, hx⟩ := hU
  obtain ⟨j, y, hy⟩ := exists_coordinate_chart
    (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ E)) x
  let e := serreIncidenceProjectiveLiftedChartPolynomialIso (K := E) j
  let m := e.hom ≫ chartι (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ E)) j
  let D := m ⁻¹ᵁ U
  have hD : (D : Set (Spec (.of (MvPolynomial (ULift.{u} {i : σ // i ≠ j}) E)))).Nonempty := by
    refine ⟨e.inv y, ?_⟩
    change m (e.inv y) ∈ U
    have he : e.hom (e.inv y) = y := by
      rw [← Scheme.Hom.comp_apply, e.inv_hom_id]
      rfl
    change (e.hom ≫ chartι _ j) (e.inv y) ∈ U
    rw [Scheme.Hom.comp_apply, he, hy]
    exact hx
  obtain ⟨v, q, hq⟩ := serreIncidenceAffineOpen_exists_ground_grid (K := K) D hD
  let qE := q ≫ m ∣_ U
  have hinc : qE ≫ U.ι = serreIncidenceProjectiveGroundPoint j
      (fun i => algebraMap K E (v i)) := by
    simp only [qE, Category.assoc, morphismRestrict_ι]
    rw [← Category.assoc, hq]
    rfl
  refine ⟨serreIncidenceProjectiveGroundPoint j v, qE,
    serreIncidenceProjectiveGroundPoint_toBase j v, ?_, ?_⟩
  · rw [← Category.assoc, hinc]
    exact serreIncidenceProjectiveGroundPoint_toBase j _
  · rw [← Category.assoc, hinc]
    exact serreIncidenceProjectiveGroundPoint_coefficient_square j v

end PfaffianDescent
