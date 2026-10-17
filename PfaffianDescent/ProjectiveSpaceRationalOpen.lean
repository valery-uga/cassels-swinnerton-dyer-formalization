import AllCharacteristics.ProjectiveSpaceCharts
import AllCharacteristics.UnirationalityCycle

/-!
# Ground-field points in nonempty opens of projective space

Over an infinite field, a nonempty open of projective space meets an affine
coordinate chart in a nonempty dense open.  Polynomial avoidance on affine
space then supplies a section over the ground field.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

section

variable {K : Type u} [Field K] {σ : Type} [Finite σ]

local notation "I₀" =>
  (⊥ : HomogeneousIdeal (homogeneousSubmodule σ K))

noncomputable def projectiveSpaceChartIsoAffineSpace (j : σ) :
    AffineSpace (ULift.{u} {i : σ // i ≠ j}) (Spec (.of K)) ≅
      Spec (.of (ChartRing I₀ j)) := by
  letI : Algebra K (ChartRing I₀ j) := (chartBaseMap I₀ j).toAlgebra
  let e₀ : MvPolynomial {i : σ // i ≠ j} K ≃ₐ[K] ChartRing I₀ j :=
    { chartPolynomialEquiv j with
      commutes' := chartPolynomialEquiv_C j }
  let e : MvPolynomial (ULift.{u} {i : σ // i ≠ j}) K ≃ₐ[K] ChartRing I₀ j :=
    (MvPolynomial.renameEquiv K Equiv.ulift).trans e₀
  exact AffineSpace.SpecIso (ULift.{u} {i : σ // i ≠ j}) (.of K) ≪≫
    Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.symm.op

theorem projectiveSpaceChartIsoAffineSpace_hom_toBase (j : σ) :
    (projectiveSpaceChartIsoAffineSpace (K := K) j).hom ≫
        Spec.map (CommRingCat.ofHom (chartBaseMap I₀ j)) =
      (AffineSpace (ULift.{u} {i : σ // i ≠ j}) (Spec (.of K)) ↘
        Spec (.of K)) := by
  letI : Algebra K (ChartRing I₀ j) := (chartBaseMap I₀ j).toAlgebra
  let e₀ : MvPolynomial {i : σ // i ≠ j} K ≃ₐ[K] ChartRing I₀ j :=
    { chartPolynomialEquiv j with
      commutes' := chartPolynomialEquiv_C j }
  let e : MvPolynomial (ULift.{u} {i : σ // i ≠ j}) K ≃ₐ[K] ChartRing I₀ j :=
    (MvPolynomial.renameEquiv K Equiv.ulift).trans e₀
  have he : e.symm.toRingHom.comp (chartBaseMap I₀ j) =
      (algebraMap K (MvPolynomial (ULift.{u} {i : σ // i ≠ j}) K)) := by
    apply RingHom.ext
    intro k
    exact e.symm.commutes k
  have hspec :
      (Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.symm.op).hom ≫
          Spec.map (CommRingCat.ofHom (chartBaseMap I₀ j)) =
        Spec.map (CommRingCat.ofHom
          (algebraMap K (MvPolynomial (ULift.{u} {i : σ // i ≠ j}) K))) := by
    simp only [Functor.mapIso_hom, Iso.op_hom, Scheme.Spec_map,
      Category.assoc, ← Spec.map_comp]
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) he
  have haff :
      (AffineSpace.SpecIso (ULift.{u} {i : σ // i ≠ j}) (.of K)).hom ≫
          Spec.map (CommRingCat.ofHom
            (algebraMap K
              (MvPolynomial (ULift.{u} {i : σ // i ≠ j}) K))) =
        (AffineSpace (ULift.{u} {i : σ // i ≠ j}) (Spec (.of K)) ↘
          Spec (.of K)) := by
    rw [← cancel_epi
      (AffineSpace.SpecIso (ULift.{u} {i : σ // i ≠ j}) (.of K)).inv]
    simp
  change ((AffineSpace.SpecIso (ULift.{u} {i : σ // i ≠ j}) (.of K)).hom ≫
      (Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.symm.op).hom) ≫ _ = _
  rw [Category.assoc, hspec, haff]

/-- Every nonempty open of projective space over an infinite field has a
ground-field section. -/
theorem nonempty_open_projectiveSpace_has_rational_section
    [Infinite K]
    (U : Scheme.Opens (scheme I₀))
    (hU : (U : Set (scheme I₀)).Nonempty) :
    ∃ q : Spec (.of K) ⟶ U,
      q ≫ U.ι ≫ toBase I₀ = 𝟙 _ := by
  obtain ⟨x, hxU⟩ := hU
  obtain ⟨j, y, hy⟩ := exists_coordinate_chart I₀ x
  let e := projectiveSpaceChartIsoAffineSpace (K := K) j
  let m : AffineSpace (ULift.{u} {i : σ // i ≠ j}) (Spec (.of K)) ⟶ scheme I₀ :=
    e.hom ≫ chartι I₀ j
  let D : Scheme.Opens
      (AffineSpace (ULift.{u} {i : σ // i ≠ j}) (Spec (.of K))) := m ⁻¹ᵁ U
  have hDne : (D : Set
      (AffineSpace (ULift.{u} {i : σ // i ≠ j}) (Spec (.of K)))).Nonempty := by
    refine ⟨e.inv y, ?_⟩
    change m (e.inv y) ∈ U
    change (e.hom ≫ chartι I₀ j) (e.inv y) ∈ U
    have hey : e.hom (e.inv y) = y := by
      rw [← Scheme.Hom.comp_apply, e.inv_hom_id]
      rfl
    rw [Scheme.Hom.comp_apply, hey, hy]
    exact hxU
  have hDdense : Dense (D : Set
      (AffineSpace (ULift.{u} {i : σ // i ≠ j}) (Spec (.of K)))) :=
    D.isOpen.dense hDne
  obtain ⟨q, hq⟩ := dense_open_affineSpace_has_rational_section D hDdense
  refine ⟨q ≫ m ∣_ U, ?_⟩
  calc
    (q ≫ m ∣_ U) ≫ U.ι ≫ toBase I₀ =
        q ≫ ((m ∣_ U) ≫ U.ι) ≫ toBase I₀ := by simp only [Category.assoc]
    _ = q ≫ (D.ι ≫ m) ≫ toBase I₀ := by rw [morphismRestrict_ι]
    _ = q ≫ D.ι ≫ m ≫ toBase I₀ := by simp only [Category.assoc]
    _ = 𝟙 _ := by
      change q ≫ D.ι ≫ (e.hom ≫ chartι I₀ j) ≫ toBase I₀ = 𝟙 _
      rw [Category.assoc e.hom, chartι_toBase]
      calc
        q ≫ D.ι ≫ e.hom ≫ Spec.map (CommRingCat.ofHom (chartBaseMap I₀ j)) =
            q ≫ D.ι ≫
              (e.hom ≫ Spec.map (CommRingCat.ofHom (chartBaseMap I₀ j))) := by
                simp only [Category.assoc]
        _ = q ≫ D.ι ≫
              (AffineSpace (ULift.{u} {i : σ // i ≠ j}) (Spec (.of K)) ↘
                Spec (.of K)) := by
                rw [projectiveSpaceChartIsoAffineSpace_hom_toBase]
        _ = 𝟙 _ := hq

end

end PfaffianDescent
