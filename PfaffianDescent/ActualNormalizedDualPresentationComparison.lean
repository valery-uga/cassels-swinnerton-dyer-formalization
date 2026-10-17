import PfaffianDescent.AmbientTensorNormalizedChartSquare
import PfaffianDescent.ActualLengthTwoDualPresentationRescaling

/-! SOURCE ONLY, UNVERIFIED. Same actual embedded component, arbitrary common
original ambient chart: epsilon comparison is derived from genuine source
isos and their true ambient presentation squares. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial Module TrivSqZeroExt
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem actual_normalized_dual_presentations_epsilon_comparison
    {Z : Scheme.{u}} (q : Z ⟶ Proj (homogeneousSubmodule (Fin 4) K))
    (x y : Fin 4 → DualNumber K) (j : Fin 4) (hx : x j = 1) (hy : y j = 1)
    (eOne eTwo : Z ≅ Spec (.of (DualNumber K)))
    (hOne : eOne.hom ≫ ambientNormalizedCoordinateChartPoint (F := K) x j hx = q)
    (hTwo : eTwo.hom ≫ ambientNormalizedCoordinateChartPoint (F := K) y j hy = q) :
    ∃ (epsilon : K) (hepsilon : epsilon ≠ 0),
      (∀ r, y r = QuarticNet.dualNumberRescaleEquiv epsilon hepsilon (x r)) ∧
      eTwo.hom ≫ Spec.map (CommRingCat.ofHom
        (QuarticNet.dualNumberRescaleEquiv epsilon hepsilon).toRingHom) = eOne.hom := by
  let pOne := ambientNormalizedCoordinateChartPoint (F := K) x j hx
  let pTwo := ambientNormalizedCoordinateChartPoint (F := K) y j hy
  let delta := eTwo.inv ≫ eOne.hom
  let deltaInv := eOne.inv ≫ eTwo.hom
  have hDeltaPoint : delta ≫ pOne = pTwo := by
    calc
      delta ≫ pOne = eTwo.inv ≫ q := by
        dsimp only [delta, pOne]
        rw [Category.assoc, hOne]
      _ = pTwo := by
        rw [← hTwo]
        simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp, pTwo]
  let f : CommRingCat.of (DualNumber K) ⟶ CommRingCat.of (DualNumber K) :=
    Spec.preimage delta
  let g : CommRingCat.of (DualNumber K) ⟶ CommRingCat.of (DualNumber K) :=
    Spec.preimage deltaInv
  have hf : Spec.map f = delta := Spec.map_preimage _
  have hg : Spec.map g = deltaInv := Spec.map_preimage _
  have hgf : g ≫ f = 𝟙 (CommRingCat.of (DualNumber K)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hf, hg, Spec.map_id]
    simp only [delta, deltaInv, Category.assoc, Iso.hom_inv_id_assoc,
      Iso.inv_hom_id]
  have hfg : f ≫ g = 𝟙 (CommRingCat.of (DualNumber K)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hf, hg, Spec.map_id]
    simp only [delta, deltaInv, Category.assoc, Iso.hom_inv_id_assoc,
      Iso.inv_hom_id]
  have hDeltaBase : delta ≫ Spec.map (CommRingCat.ofHom (algebraMap K (DualNumber K))) =
      Spec.map (CommRingCat.ofHom (algebraMap K (DualNumber K))) := by
    calc
      delta ≫ Spec.map (CommRingCat.ofHom (algebraMap K (DualNumber K))) =
          delta ≫ (pOne ≫ ambientToBase (R := K)) := by
        exact congrArg (fun a => delta ≫ a)
          (ambientNormalizedCoordinateChartPoint_toBase x j hx).symm
      _ = (delta ≫ pOne) ≫ ambientToBase (R := K) := (Category.assoc _ _ _).symm
      _ = pTwo ≫ ambientToBase (R := K) := by rw [hDeltaPoint]
      _ = Spec.map (CommRingCat.ofHom (algebraMap K (DualNumber K))) :=
        ambientNormalizedCoordinateChartPoint_toBase y j hy
  have hBaseCat : CommRingCat.ofHom (algebraMap K (DualNumber K)) ≫ f =
      CommRingCat.ofHom (algebraMap K (DualNumber K)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hf]
    exact hDeltaBase
  let ringE : DualNumber K ≃+* DualNumber K := RingEquiv.ofRingHom f.hom g.hom
    (by exact congrArg CommRingCat.Hom.hom hgf)
    (by exact congrArg CommRingCat.Hom.hom hfg)
  let algE : DualNumber K ≃ₐ[K] DualNumber K :=
    AlgEquiv.ofRingEquiv (f := ringE) (by
      intro c
      exact congrArg (fun a : CommRingCat.of K ⟶ CommRingCat.of (DualNumber K) => a.hom c) hBaseCat)
  obtain ⟨c, hc, hScale⟩ := QuarticNet.dualNumberAlgEquiv_is_actual_rescaling algE
  let chart := Proj.awayι (homogeneousSubmodule (Fin 4) K) (X j)
    (isHomogeneous_X K j) (by decide : 0 < 1)
  letI : IsOpenImmersion chart := by
    dsimp only [chart, Proj.awayι]
    infer_instance
  have hChartSquare :
      Spec.map (CommRingCat.ofHom (ambientNormalizedCoordinateChartMap x j hx) ≫ f) ≫ chart =
        Spec.map (CommRingCat.ofHom (ambientNormalizedCoordinateChartMap y j hy)) ≫ chart := by
    rw [Spec.map_comp, hf, Category.assoc]
    exact hDeltaPoint
  have hMaps : CommRingCat.ofHom (ambientNormalizedCoordinateChartMap x j hx) ≫ f =
      CommRingCat.ofHom (ambientNormalizedCoordinateChartMap y j hy) :=
    Spec.map_injective ((cancel_mono chart).mp hChartSquare)
  have hCoordinates (r : Fin 4) : algE (x r) = y r := by
    have h := congrArg (fun a : CommRingCat.of
      (HomogeneousLocalization.Away (homogeneousSubmodule (Fin 4) K) (X j)) ⟶
        CommRingCat.of (DualNumber K) => a.hom (ambientChartCoordinate (R := K) j r)) hMaps
    change f.hom (ambientNormalizedCoordinateChartMap x j hx
      (ambientChartCoordinate (R := K) j r)) =
        ambientNormalizedCoordinateChartMap y j hy (ambientChartCoordinate (R := K) j r) at h
    rw [ambientNormalizedCoordinateChartMap_coordinate,
      ambientNormalizedCoordinateChartMap_coordinate] at h
    exact h
  refine ⟨c, hc, ?_, ?_⟩
  · intro r
    exact (hCoordinates r).symm.trans (congrArg (fun e : DualNumber K ≃ₐ[K] DualNumber K => e (x r)) hScale)
  · have hScaleCat : f = CommRingCat.ofHom
        (QuarticNet.dualNumberRescaleEquiv c hc).toRingHom := by
      change CommRingCat.ofHom algE.toRingHom = _
      rw [hScale]
    rw [← hScaleCat, hf]
    simp only [delta, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

end PfaffianDescent
