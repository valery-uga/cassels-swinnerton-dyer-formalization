import PfaffianDescent.SingleSupportLengthTwoDualCoordinates
import PfaffianDescent.RationalAffineChartPointFaithfulness

/-! Every supplied length-two component at a coordinate vertex is its OWN
actual nonzero tangent double point. Vertex residues follow from its support;
neither tangent coordinates nor an embedding comparison is assumed. -/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial Module TrivSqZeroExt
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

def coordinateVertexCoordinates (row r : Fin 4) : K := if row = r then 1 else 0

def coordinateVertexChartHom (row : Fin 4) :
    ChartRing (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) row →+* K :=
  normalizedPointChartMap ⊥ (coordinateVertexCoordinates row) row
    (by simp [coordinateVertexCoordinates]) (by
      intro p hp
      simp [Ideal.mem_bot.mp hp])

def coordinateVertexMap (row : Fin 4) : Spec (.of K) ⟶
    scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) :=
  Spec.map (CommRingCat.ofHom (coordinateVertexChartHom row)) ≫ chartι ⊥ row

def coordinateVertex (row : Fin 4) :
    scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) :=
  coordinateVertexMap row (IsLocalRing.closedPoint K)

/-- Literal fixed-vertex tangent parametrization for EVERY supplied local
length-two component over an algebraically closed field. The conclusion
retains its specified original closed immersion in ambient projective space. -/
theorem coordinateVertex_lengthTwo_actual_tangent [IsAlgClosed K]
    {Z : Scheme.{u}}
    (i : Z ⟶ scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)))
    [IsClosedImmersion i] [IsFinite (i ≫ toBase ⊥)] (row : Fin 4)
    (hSupport : Set.range i = {coordinateVertex (K := K) row})
    (hZ : AllCharacteristics.finiteSchemeRank (i ≫ toBase ⊥) = 2) :
    ∃ (e : Z ≅ Spec (.of (DualNumber K))) (u : Fin 4 → K) (hu : u row = 0),
      u ≠ 0 ∧
      e.hom ≫ ambientNormalizedCoordinateChartPoint (F := K)
        (fun r => TrivSqZeroExt.inl (coordinateVertexCoordinates (K := K) row r) +
          TrivSqZeroExt.inr (u r)) row
        (by simp [coordinateVertexCoordinates, hu]) = i ≫ quotientProjMap ⊥ := by
  let I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K) := ⊥
  letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ toBase I)
  letI := finiteSchemeCoefficientAlgebra (i ≫ toBase I)
  letI := finiteSchemeCoefficient_finite (i ≫ toBase I)
  letI : IsLocalRing Γ(Z, ⊤) :=
    singleSupport_globalSections_isLocalRing i (coordinateVertex row) hSupport
  have hA : finrank K Γ(Z, ⊤) = 2 :=
    (finiteSchemeCoefficient_finrank (i ≫ toBase I)).trans hZ
  obtain ⟨e0⟩ := lengthTwoLocal_dual_equiv hA
  let eA := e0.symm
  have hiVertex (z : Z) : i z = coordinateVertex (K := K) row := by
    apply Set.mem_singleton_iff.mp
    rw [← hSupport]
    exact Set.mem_range_self z
  have hrange : Set.range i ⊆ Set.range (chartι I row) := by
    rintro _ ⟨z, rfl⟩
    refine ⟨Spec.map (CommRingCat.ofHom (coordinateVertexChartHom row))
      (IsLocalRing.closedPoint K), ?_⟩
    exact (hiVertex z).symm
  let iU := IsOpenImmersion.lift (chartι I row) i hrange
  have hU : iU ≫ chartι I row = i := IsOpenImmersion.lift_fac _ _ _
  letI : IsClosedImmersion (iU ≫ chartι I row) := hU.symm ▸ inferInstance
  letI : IsClosedImmersion iU := IsClosedImmersion.of_comp iU (chartι I row)
  let g := Spec.preimage (Z.isoSpec.inv ≫ iU)
  have hg : Spec.map g = Z.isoSpec.inv ≫ iU := Spec.map_preimage _
  have hgPoint : Spec.map g ≫ chartι I row = Z.isoSpec.inv ≫ i := by
    rw [hg, Category.assoc, hU]
  have hgb : g.hom.comp (chartBaseMap I row) = algebraMap K Γ(Z, ⊤) := by
    have h : CommRingCat.ofHom (chartBaseMap I row) ≫ g =
        CommRingCat.ofHom (algebraMap K Γ(Z, ⊤)) := by
      apply Spec.map_injective
      rw [Spec.map_comp, hg, ← chartι_toBase, finiteSchemeCoefficient_spec]
      have hUbase : iU ≫ chartι I row ≫ toBase I = i ≫ toBase I := by
        rw [← Category.assoc, hU]
      rw [Category.assoc, hUbase]
    exact congrArg CommRingCat.Hom.hom h
  let x : Fin 4 → Γ(Z, ⊤) := fun r => g.hom (chartCoordinate I row r)
  have hx : x row = 1 := by simp only [x, chartCoordinate_self, map_one]
  let rho : Γ(Z, ⊤) →ₐ[K] K := (TrivSqZeroExt.fstHom K K K).comp eA.toAlgHom
  let f : ChartRing I row →+* K := rho.toRingHom.comp g.hom
  let gv := coordinateVertexChartHom (K := K) row
  have hfbase : f.comp (chartBaseMap I row) = RingHom.id K := by
    change rho.toRingHom.comp (g.hom.comp (chartBaseMap I row)) = RingHom.id K
    rw [hgb]
    ext c
    exact rho.commutes c
  have hgvbase : gv.comp (chartBaseMap I row) = RingHom.id K := by
    ext c
    exact normalizedPointChartMap_base ⊥ (coordinateVertexCoordinates row) row
      (by simp [coordinateVertexCoordinates]) _ c
  have hfPoint : Spec.map (CommRingCat.ofHom f) ≫ chartι I row =
      Spec.map (CommRingCat.ofHom rho.toRingHom) ≫ Z.isoSpec.inv ≫ i := by
    rw [show CommRingCat.ofHom f = g ≫ CommRingCat.ofHom rho.toRingHom from rfl,
      Spec.map_comp, Category.assoc, hgPoint]
  have hpoint : Spec.map (CommRingCat.ofHom f) (IsLocalRing.closedPoint K) =
      Spec.map (CommRingCat.ofHom gv) (IsLocalRing.closedPoint K) := by
    apply (chartι I row).isOpenEmbedding.injective
    calc
      chartι I row (Spec.map (CommRingCat.ofHom f) (IsLocalRing.closedPoint K)) =
          (Spec.map (CommRingCat.ofHom f) ≫ chartι I row) (IsLocalRing.closedPoint K) := rfl
      _ = (Spec.map (CommRingCat.ofHom rho.toRingHom) ≫ Z.isoSpec.inv ≫ i)
          (IsLocalRing.closedPoint K) := congrArg (fun t => t (IsLocalRing.closedPoint K)) hfPoint
      _ = coordinateVertex row := hiVertex _
      _ = chartι I row (Spec.map (CommRingCat.ofHom gv) (IsLocalRing.closedPoint K)) := rfl
  have hfg : f = gv := fieldValueRingHom_eq_of_same_spec_point
    (chartBaseMap I row) f gv hfbase hgvbase hpoint
  have hresidue (r : Fin 4) : (eA (x r)).fst = coordinateVertexCoordinates row r := by
    have h := DFunLike.congr_fun hfg (chartCoordinate I row r)
    change (eA (x r)).fst = coordinateVertexChartHom row (chartCoordinate I row r) at h
    rw [coordinateVertexChartHom, normalizedPointChartMap_coordinate] at h
    exact h
  have hgs : Function.Surjective g.hom :=
    AllCharacteristics.spec_preimage_surjective_of_closedImmersion (Z.isoSpec.inv ≫ iU)
  have hgen : Function.Surjective (aeval (R := K) x) := by
    have heval : (aeval (R := K) x).toRingHom =
        g.hom.comp (eval₂Hom (chartBaseMap I row) (chartCoordinate I row)) := by
      apply RingHom.ext
      intro p
      change p.eval₂ (algebraMap K Γ(Z, ⊤)) x = g.hom (p.eval₂ _ _)
      rw [hom_eval₂, hgb]
    change Function.Surjective (aeval (R := K) x).toRingHom
    rw [heval]
    exact hgs.comp (eval₂_chartCoordinate_surjective I row)
  let u : Fin 4 → K := fun r => (eA (x r)).snd
  have hu : u row = 0 := by simp [u, hx]
  have hcoords (r : Fin 4) : eA (x r) =
      TrivSqZeroExt.inl (coordinateVertexCoordinates (K := K) row r) +
        TrivSqZeroExt.inr (u r) := by
    apply TrivSqZeroExt.ext <;> simp [u, hresidue]
  have hcomp : eA.toAlgHom.comp (aeval (R := K) x) =
      aeval (R := K) (fun r => eA (x r)) := by
    apply MvPolynomial.algHom_ext
    intro r
    simp only [AlgHom.comp_apply, aeval_X]
    rfl
  have hdualgen : Function.Surjective (aeval (R := K) (fun r => eA (x r))) := by
    rw [← hcomp]
    exact eA.surjective.comp hgen
  have huNe : u ≠ 0 := by
    intro hu0
    have hconstant : aeval (R := K) (fun r => eA (x r)) =
        (TrivSqZeroExt.inlAlgHom K K K).comp (aeval (R := K) (coordinateVertexCoordinates row)) := by
      apply MvPolynomial.algHom_ext
      intro r
      rw [AlgHom.comp_apply, aeval_X, aeval_X, hcoords r, congrFun hu0 r]
      simp
    obtain ⟨p, hp⟩ := hdualgen (TrivSqZeroExt.inr (1 : K))
    rw [hconstant] at hp
    have h := congrArg TrivSqZeroExt.snd hp
    exact (zero_ne_one : (0 : K) ≠ 1) (by simpa using h)
  let eSpec := Scheme.Spec.mapIso eA.toRingEquiv.toCommRingCatIso.symm.op
  let e := Z.isoSpec ≪≫ eSpec
  have hq : ambientNormalizedCoordinateChartPoint (F := K)
      (fun r => eA (x r)) row (by rw [hx, map_one]) =
      e.inv ≫ i ≫ quotientProjMap I := by
    change ambientNormalizedCoordinateChartPoint (F := K)
      (fun r => eA.toAlgHom (x r)) row _ = e.inv ≫ i ≫ quotientProjMap I
    rw [ambientNormalizedCoordinateChartPoint_algHom eA.toAlgHom x row hx,
      ambientNormalizedCoordinateChartPoint_eq_original_chart I row g.hom hgb]
    change Spec.map (CommRingCat.ofHom eA.toRingHom) ≫ Spec.map g ≫
      chartι I row ≫ quotientProjMap I = _
    rw [← Category.assoc (Spec.map g), hgPoint]
    rfl
  have hy : (fun r => eA (x r)) =
      (fun r => TrivSqZeroExt.inl (coordinateVertexCoordinates (K := K) row r) +
        TrivSqZeroExt.inr (u r)) := funext hcoords
  have hpointEq : ambientNormalizedCoordinateChartPoint (F := K)
      (fun r => eA (x r)) row (by rw [hx, map_one]) =
    ambientNormalizedCoordinateChartPoint (F := K)
      (fun r => TrivSqZeroExt.inl (coordinateVertexCoordinates (K := K) row r) +
        TrivSqZeroExt.inr (u r)) row
      (by simp [coordinateVertexCoordinates, hu]) := by
    have hcongr (a b : Fin 4 → DualNumber K) (ha : a row = 1) (hb : b row = 1)
        (hab : a = b) : ambientNormalizedCoordinateChartPoint (F := K) a row ha =
          ambientNormalizedCoordinateChartPoint (F := K) b row hb := by
      subst b
      rfl
    exact hcongr _ _ _ _ hy
  refine ⟨e, u, hu, huNe, ?_⟩
  rw [← hpointEq, hq]
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rfl

end PfaffianDescent
