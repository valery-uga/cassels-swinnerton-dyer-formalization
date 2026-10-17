import PfaffianDescent.CoordinateVertexLengthTwoActualTangent
import PfaffianDescent.ActualLengthTwoDualPresentationRescaling

/-! SOURCE-ONLY UNVERIFIED isolated check unit. This is an alternative
split of the previously supplied TMP draft, with the same declarations.
Do not import the old monolithic version alongside this split. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Module TrivSqZeroExt
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem coordinateVertex_supplied_epsilon_presentations_rescale
    {Z : Scheme.{u}}
    (q : Z ⟶ Proj (homogeneousSubmodule (Fin 4) K)) (row : Fin 4)
    (u v : Fin 4 → K) (hu : u row = 0) (hv : v row = 0)
    (eOne eTwo : Z ≅ Spec (.of (DualNumber K)))
    (hOne : eOne.hom ≫ ambientNormalizedCoordinateChartPoint (F := K)
      (fun r => inl (coordinateVertexCoordinates (K := K) row r) + inr (u r)) row
      (by simp [coordinateVertexCoordinates, hu]) = q)
    (hTwo : eTwo.hom ≫ ambientNormalizedCoordinateChartPoint (F := K)
      (fun r => inl (coordinateVertexCoordinates (K := K) row r) + inr (v r)) row
      (by simp [coordinateVertexCoordinates, hv]) = q) :
    ∃ (c : K) (hc : c ≠ 0),
      (∀ r, v r = c * u r) ∧
      eTwo.hom ≫ Spec.map (CommRingCat.ofHom
        (QuarticNet.dualNumberRescaleEquiv c hc).toRingHom) = eOne.hom := by
  let x : Fin 4 → DualNumber K := fun r =>
    inl (coordinateVertexCoordinates (K := K) row r) + inr (u r)
  let y : Fin 4 → DualNumber K := fun r =>
    inl (coordinateVertexCoordinates (K := K) row r) + inr (v r)
  have hx : x row = 1 := by simp [x, coordinateVertexCoordinates, hu]
  have hy : y row = 1 := by simp [y, coordinateVertexCoordinates, hv]
  let pOne := ambientNormalizedCoordinateChartPoint (F := K) x row hx
  let pTwo := ambientNormalizedCoordinateChartPoint (F := K) y row hy
  let delta := eTwo.inv ≫ eOne.hom
  let deltaInv := eOne.inv ≫ eTwo.hom
  have hDeltaPoint : delta ≫ pOne = pTwo := by
    calc
      delta ≫ pOne = eTwo.inv ≫ q := by
        dsimp only [delta, pOne]
        rw [Category.assoc, hOne]
      _ = pTwo := by
        rw [← hTwo]
        simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
        rfl
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
          (ambientNormalizedCoordinateChartPoint_toBase x row hx).symm
      _ = (delta ≫ pOne) ≫ ambientToBase (R := K) := (Category.assoc _ _ _).symm
      _ = pTwo ≫ ambientToBase (R := K) := by rw [hDeltaPoint]
      _ = Spec.map (CommRingCat.ofHom (algebraMap K (DualNumber K))) :=
        ambientNormalizedCoordinateChartPoint_toBase y row hy
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
  let chart := Proj.awayι (homogeneousSubmodule (Fin 4) K) (X row)
    (isHomogeneous_X K row) (by decide : 0 < 1)
  letI : IsOpenImmersion chart := by
    dsimp only [chart, Proj.awayι]
    infer_instance
  have hChartSquare :
      Spec.map (CommRingCat.ofHom (ambientNormalizedCoordinateChartMap (F := K) x row hx) ≫ f) ≫ chart =
        Spec.map (CommRingCat.ofHom (ambientNormalizedCoordinateChartMap (F := K) y row hy)) ≫ chart := by
    rw [Spec.map_comp, hf, Category.assoc]
    exact hDeltaPoint
  have hMaps : CommRingCat.ofHom (ambientNormalizedCoordinateChartMap (F := K) x row hx) ≫ f =
      CommRingCat.ofHom (ambientNormalizedCoordinateChartMap (F := K) y row hy) :=
    Spec.map_injective ((cancel_mono chart).mp hChartSquare)
  have hCoordinates (r : Fin 4) : algE (x r) = y r := by
    have h := congrArg (fun a : CommRingCat.of
      (HomogeneousLocalization.Away (homogeneousSubmodule (Fin 4) K) (X row)) ⟶
        CommRingCat.of (DualNumber K) => a.hom (ambientChartCoordinate (R := K) row r)) hMaps
    change f.hom (ambientNormalizedCoordinateChartMap (F := K) x row hx
      (ambientChartCoordinate (R := K) row r)) =
        ambientNormalizedCoordinateChartMap (F := K) y row hy (ambientChartCoordinate (R := K) row r) at h
    rw [ambientNormalizedCoordinateChartMap_coordinate,
      ambientNormalizedCoordinateChartMap_coordinate] at h
    exact h
  refine ⟨c, hc, ?_, ?_⟩
  · intro r
    have h := hCoordinates r
    rw [hScale] at h
    have hsnd := congrArg TrivSqZeroExt.snd h
    change (QuarticNet.dualNumberRescale c (x r)).snd = (y r).snd at hsnd
    simpa [x, y, QuarticNet.dualNumberRescale, TrivSqZeroExt.snd_map,
      LinearMap.mulLeft_apply, mul_comm] using hsnd.symm
  · have hScaleCat : f = CommRingCat.ofHom
        (QuarticNet.dualNumberRescaleEquiv c hc).toRingHom := by
      change CommRingCat.ofHom algE.toRingHom = _
      rw [hScale]
    rw [← hScaleCat, hf]
    simp only [delta, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

end PfaffianDescent
