import PfaffianDescent.CorayLiteralModelIncidenceReduced
import PfaffianDescent.FiniteSchemeAlgebra
import AllCharacteristics.FiniteSchemeBaseChangeRank
import Mathlib.RingTheory.Etale.Field
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! Source only: the native geometric fibre of the SAME entire incidence.
Reducedness and ranks are retained on the literal scheme, without selecting
an incident closed point or assuming component-point transitivity. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A finite formally unramified scheme over an algebraically closed field
has rank equal to the cardinality of its ACTUAL carrier. The coordinate
algebra is the native global-section algebra, not a chosen reduced algebra. -/
theorem finiteFormallyUnramifiedScheme_overAlgClosed_rank_eq_carrierCard
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] {X : Scheme.{u}}
    (pi : X ⟶ Spec (.of Ω)) [IsFinite pi] [FormallyUnramified pi] :
    finiteSchemeRank pi = Nat.card X := by
  letI : IsAffine X := isAffine_of_isAffineHom pi
  letI := finiteSchemeCoefficientAlgebra pi
  letI : Module.Finite Ω Γ(X, ⊤) := finiteSchemeCoefficient_finite pi
  have hspec : FormallyUnramified
      (Spec.map (CommRingCat.ofHom (algebraMap Ω Γ(X, ⊤)))) := by
    rw [finiteSchemeCoefficient_spec pi]
    exact MorphismProperty.comp_mem (@FormallyUnramified.{u})
      X.isoSpec.inv pi inferInstance inferInstance
  letI : Algebra.FormallyUnramified Ω Γ(X, ⊤) :=
    (HasRingHomProperty.Spec_iff (P := @FormallyUnramified.{u})).mp hspec
  letI : Algebra.FormallyEtale Ω Γ(X, ⊤) :=
    Algebra.FormallyEtale.of_formallyUnramified_of_field Ω Γ(X, ⊤)
  letI : IsArtinianRing Γ(X, ⊤) := IsArtinianRing.of_finite Ω Γ(X, ⊤)
  letI : Fintype (PrimeSpectrum Γ(X, ⊤)) := Fintype.ofFinite _
  let e := Algebra.FormallyEtale.equivPiOfIsSepClosed Ω Γ(X, ⊤)
  calc
    finiteSchemeRank pi = Module.finrank Ω Γ(X, ⊤) := (finiteSchemeCoefficient_finrank pi).symm
    _ = Module.finrank Ω (PrimeSpectrum Γ(X, ⊤) → Ω) := e.toLinearEquiv.finrank_eq
    _ = Fintype.card (PrimeSpectrum Γ(X, ⊤)) := Module.finrank_fintype_fun_eq_card Ω
    _ = Nat.card (PrimeSpectrum Γ(X, ⊤)) := (Nat.card_eq_fintype_card).symm
    _ = Nat.card X := Nat.card_congr X.isoSpec.hom.homeomorph.toEquiv.symm

/-- The native map between original-base changes. -/
def nativeOriginalBaseChangeMap {X T S O : Scheme.{u}}
    (f : X ⟶ T) (p : T ⟶ S) (b : O ⟶ S) :
    pullback (f ≫ p) b ⟶ pullback p b :=
  pullback.lift (pullback.fst (f ≫ p) b ≫ f) (pullback.snd (f ≫ p) b)
    (by rw [Category.assoc, pullback.condition])

/-- The actual scalar-compatible lift of the original point into the
native original-base change. -/
def nativeOriginalPointGeometricLift {R T S O : Scheme.{u}}
    (ep : R ⟶ T) (p : T ⟶ S) (b : O ⟶ S) (v : O ⟶ R)
    (hv : v ≫ ep ≫ p = b) : O ⟶ pullback p b :=
  pullback.lift (v ≫ ep) (𝟙 O) (by simpa only [Category.assoc, Category.id_comp] using hv)

/-- The native map from the geometric base change of the literal entire
incidence into the original-base change of the SAME model scheme. -/
def nativeEntireIncidenceToOriginalBaseChange {X R T S O : Scheme.{u}}
    (ep : R ⟶ T) (f : X ⟶ T) (p : T ⟶ S) (b : O ⟶ S) (v : O ⟶ R)
    (hv : v ≫ ep ≫ p = b) :
    pullback (pullback.fst ep f) v ⟶ pullback (f ≫ p) b :=
  pullback.lift
    (pullback.fst (pullback.fst ep f) v ≫ pullback.snd ep f)
    (pullback.snd (pullback.fst ep f) v) (by
      calc
        (pullback.fst (pullback.fst ep f) v ≫ pullback.snd ep f) ≫ (f ≫ p) =
            pullback.fst (pullback.fst ep f) v ≫ (pullback.snd ep f ≫ f) ≫ p := by
          simp only [Category.assoc]
        _ = pullback.fst (pullback.fst ep f) v ≫ (pullback.fst ep f ≫ ep) ≫ p := by
          rw [← pullback.condition (f := ep) (g := f)]
        _ = (pullback.fst (pullback.fst ep f) v ≫ pullback.fst ep f) ≫ ep ≫ p := by
          simp only [Category.assoc]
        _ = (pullback.snd (pullback.fst ep f) v ≫ v) ≫ ep ≫ p := by
          rw [pullback.condition]
        _ = pullback.snd (pullback.fst ep f) v ≫ (v ≫ ep ≫ p) := by
          simp only [Category.assoc]
        _ = pullback.snd (pullback.fst ep f) v ≫ b := by rw [hv])

/-- The SAME base-changed entire incidence is the actual geometric-point
fibre of the native map between original-base changes. This square is
CONSTRUCTED by native Cartesian cancellation and paste_twist_right. No
fibre identification, coproduct, image equality or incidence count premise. -/
theorem nativeEntireIncidence_originalBaseChange_isPullback
    {X R T S O : Scheme.{u}}
    (ep : R ⟶ T) (f : X ⟶ T) (p : T ⟶ S) (b : O ⟶ S) (v : O ⟶ R)
    (hv : v ≫ ep ≫ p = b) :
    IsPullback (nativeEntireIncidenceToOriginalBaseChange ep f p b v hv)
      (pullback.snd (pullback.fst ep f) v)
      (nativeOriginalBaseChangeMap f p b)
      (nativeOriginalPointGeometricLift ep p b v hv) := by
  let W := pullback (f ≫ p) b
  let F := nativeOriginalBaseChangeMap f p b
  let q := nativeOriginalPointGeometricLift ep p b v hv
  let B := nativeEntireIncidenceToOriginalBaseChange ep f p b v hv
  have Hfi : IsPullback (pullback.fst (f ≫ p) b) F f (pullback.fst p b) := by
    have hFfst : F ≫ pullback.fst p b = pullback.fst (f ≫ p) b ≫ f := by
      dsimp only [F, nativeOriginalBaseChangeMap]
      exact pullback.lift_fst _ _ _
    have hFsnd : F ≫ pullback.snd p b = pullback.snd (f ≫ p) b := by
      dsimp only [F, nativeOriginalBaseChangeMap]
      exact pullback.lift_snd _ _ _
    have Hwide : IsPullback (pullback.fst (f ≫ p) b) (F ≫ pullback.snd p b)
        (f ≫ p) b := by
      rw [hFsnd]
      exact IsPullback.of_hasPullback (f ≫ p) b
    exact IsPullback.of_bot Hwide hFfst.symm (IsPullback.of_hasPullback p b)
  have hpoint : v ≫ ep = q ≫ pullback.fst p b := by
    dsimp only [q, nativeOriginalPointGeometricLift]
    exact (pullback.lift_fst _ _ _).symm
  have hBfst : B ≫ pullback.fst (f ≫ p) b =
      pullback.fst (pullback.fst ep f) v ≫ pullback.snd ep f := by
    dsimp only [B, nativeEntireIncidenceToOriginalBaseChange]
    exact pullback.lift_fst _ _ _
  have hBsnd : B ≫ F = pullback.snd (pullback.fst ep f) v ≫ q := by
    apply pullback.hom_ext
    · calc
        (B ≫ F) ≫ pullback.fst p b = B ≫ (pullback.fst (f ≫ p) b ≫ f) := by
          rw [Category.assoc, show F ≫ pullback.fst p b =
            pullback.fst (f ≫ p) b ≫ f from pullback.lift_fst _ _ _]
        _ = (B ≫ pullback.fst (f ≫ p) b) ≫ f := (Category.assoc _ _ _).symm
        _ = (pullback.fst (pullback.fst ep f) v ≫ pullback.snd ep f) ≫ f := by rw [hBfst]
        _ = pullback.fst (pullback.fst ep f) v ≫ (pullback.snd ep f ≫ f) := Category.assoc _ _ _
        _ = pullback.fst (pullback.fst ep f) v ≫ (pullback.fst ep f ≫ ep) := by
          rw [← pullback.condition (f := ep) (g := f)]
        _ = (pullback.fst (pullback.fst ep f) v ≫ pullback.fst ep f) ≫ ep := (Category.assoc _ _ _).symm
        _ = (pullback.snd (pullback.fst ep f) v ≫ v) ≫ ep := by rw [pullback.condition]
        _ = pullback.snd (pullback.fst ep f) v ≫ (v ≫ ep) := Category.assoc _ _ _
        _ = pullback.snd (pullback.fst ep f) v ≫ (q ≫ pullback.fst p b) := by rw [hpoint]
        _ = (pullback.snd (pullback.fst ep f) v ≫ q) ≫ pullback.fst p b := (Category.assoc _ _ _).symm
    · dsimp only [B, F, q, nativeEntireIncidenceToOriginalBaseChange,
        nativeOriginalBaseChangeMap, nativeOriginalPointGeometricLift]
      simp only [Category.assoc, pullback.lift_snd, Category.comp_id]
  exact IsPullback.paste_twist_right
    (IsPullback.of_hasPullback ep f).flip Hfi v q hpoint
    (pullback.fst (pullback.fst ep f) v) (pullback.snd (pullback.fst ep f) v)
    (IsPullback.of_hasPullback (pullback.fst ep f) v) hBfst hBsnd

/-- Over a one-point geometric spectrum, the native whole-incidence fibre
maps as a closed immersion onto the literal inverse image of that point.
The resulting carrier equivalence is built from the ACTUAL map and range. -/
theorem nativeEntireIncidence_originalBaseChange_supportEquiv
    {Ω : Type u} [Field Ω] {X R T S : Scheme.{u}}
    (ep : R ⟶ T) (f : X ⟶ T) (p : T ⟶ S)
    (b : Spec (.of Ω) ⟶ S) (v : Spec (.of Ω) ⟶ R)
    (hv : v ≫ ep ≫ p = b) :
    let q := nativeOriginalPointGeometricLift ep p b v hv
    let B := nativeEntireIncidenceToOriginalBaseChange ep f p b v hv
    let F := nativeOriginalBaseChangeMap f p b
    IsClosedImmersion B ∧
      ∃ e : ↥(pullback (pullback.fst ep f) v : Scheme.{u}) ≃
        {y : ↥(pullback (f ≫ p) b : Scheme.{u}) | F y = q (IsLocalRing.closedPoint Ω)},
        ∀ z, (e z).1 = B z := by
  let q := nativeOriginalPointGeometricLift ep p b v hv
  let B := nativeEntireIncidenceToOriginalBaseChange ep f p b v hv
  let F := nativeOriginalBaseChangeMap f p b
  have hq : q ≫ pullback.snd p b = 𝟙 _ := pullback.lift_snd _ _ _
  letI : IsClosedImmersion q := isClosedImmersion_of_comp_eq_id (pullback.snd p b) q hq
  have H := nativeEntireIncidence_originalBaseChange_isPullback ep f p b v hv
  letI : IsClosedImmersion B :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion.{u}) H.flip inferInstance
  have hrange : Set.range B = F ⁻¹' Set.range q := by
    change Set.range (nativeEntireIncidenceToOriginalBaseChange ep f p b v hv) = _
    rw [← H.isoPullback_hom_fst]
    change Set.range (fun z => pullback.fst F q (H.isoPullback.hom z)) = _
    have hIsoSurj : Function.Surjective H.isoPullback.hom :=
      H.isoPullback.hom.homeomorph.surjective
    rw [Set.range_comp', Set.range_eq_univ.mpr hIsoSurj,
      Set.image_univ, Scheme.Pullback.range_fst]
  have hqrange : Set.range q = {q (IsLocalRing.closedPoint Ω)} := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact congrArg q (Subsingleton.elim x (IsLocalRing.closedPoint Ω))
    · intro hy
      exact ⟨IsLocalRing.closedPoint Ω, hy.symm⟩
  have hB (z : ↥(pullback (pullback.fst ep f) v : Scheme.{u})) : F (B z) = q (IsLocalRing.closedPoint Ω) := by
    have hz : B z ∈ Set.range B := ⟨z, rfl⟩
    rw [hrange, hqrange] at hz
    exact hz
  let g : ↥(pullback (pullback.fst ep f) v : Scheme.{u}) →
      {y : ↥(pullback (f ≫ p) b : Scheme.{u}) | F y = q (IsLocalRing.closedPoint Ω)} := fun z => ⟨B z, hB z⟩
  have hinj : Function.Injective g := by
    intro z w h
    exact B.isClosedEmbedding.injective (congrArg Subtype.val h)
  have hsurj : Function.Surjective g := by
    intro y
    have hy : y.1 ∈ Set.range B := by
      rw [hrange, hqrange]
      exact y.2
    obtain ⟨z, hz⟩ := hy
    exact ⟨z, Subtype.ext hz⟩
  exact ⟨inferInstance, Equiv.ofBijective g ⟨hinj, hsurj⟩, fun _ => rfl⟩

variable {K M Ω : Type u} [Field K] [CharZero K] [Field M] [Field Ω]
  [Algebra K M] [Module.Finite K M] [Algebra K Ω] [IsAlgClosed Ω]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- An actual original-K residue embedding of SAME original closed P gives
its ACTUAL geometric lift into the native I base change. Its image back in
original I is P, proved on the literal maps. No unrelated geometric point. -/
theorem originalPointModelIncidence_residueEmbedding_geometricLift
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (P : closedPoints (scheme I))
    (psi : letI := pointAlgebra (toBase I) P.1; (scheme I).residueField P.1 →ₐ[K] Ω) :
    letI := pointAlgebra (toBase I) P.1
    let ep := (scheme I).fromSpecResidueField P.1
    let b := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
    let v := Spec.map (CommRingCat.ofHom psi.toRingHom)
    ∃ hv : v ≫ ep ≫ toBase I = b,
      let q := nativeOriginalPointGeometricLift ep (toBase I) b v hv
      q ≫ pullback.snd (toBase I) b = 𝟙 _ ∧
        pullback.fst (toBase I) b (q (IsLocalRing.closedPoint Ω)) = P.1 := by
  letI := pointAlgebra (toBase I) P.1
  let ep := (scheme I).fromSpecResidueField P.1
  let b := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
  let v := Spec.map (CommRingCat.ofHom psi.toRingHom)
  have hv : v ≫ ep ≫ toBase I = b := by
    rw [← pointAlgebra_spec (toBase I) P.1, ← Spec.map_comp]
    congr 1
    ext k
    exact psi.commutes k
  refine ⟨hv, pullback.lift_snd _ _ _, ?_⟩
  have hmap : nativeOriginalPointGeometricLift ep (toBase I) b v hv ≫
      pullback.fst (toBase I) b = v ≫ ep := pullback.lift_fst _ _ _
  have happ := congrArg (fun m => m (IsLocalRing.closedPoint Ω)) hmap
  simp only [Scheme.Hom.comp_apply] at happ
  have hpoint : ep (v (IsLocalRing.closedPoint Ω)) = P.1 :=
    Scheme.fromSpecResidueField_apply P.1 (v (IsLocalRing.closedPoint Ω))
  change pullback.fst (toBase I) b
    (nativeOriginalPointGeometricLift ep (toBase I) b v hv
      (IsLocalRing.closedPoint Ω)) = P.1
  exact happ.trans hpoint

/-- The ACTUAL kappa(P)-rank s of the SAME literal entire incidence equals
the cardinality of the actual geometric-point fibre on SAME D viewed over
original K. Finite unramified base change PROVES reduced field factors; the
native support equivalence retains the whole incidence and same original P.
No coproduct, component count, positivity, point orbit or small-count premise. -/
theorem originalPointModelIncidence_residueRank_eq_geometricFiberCard
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (D : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) M))
    (hID : (I.map (componentPolynomialCoefficientMap (algebraMap K M))).toIdeal ≤ D.toIdeal)
    (P : closedPoints (scheme I))
    (psi : letI := pointAlgebra (toBase I) P.1; (scheme I).residueField P.1 →ₐ[K] Ω) :
    letI := pointAlgebra (toBase I) P.1
    let ep := (scheme I).fromSpecResidueField P.1
    let f := coefficientComponentToOriginal I D hID
    let c := pullback.fst ep f
    let b := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
    let v := Spec.map (CommRingCat.ofHom psi.toRingHom)
    ∃ hfinite : IsFinite c, ∃ hv : v ≫ ep ≫ toBase I = b,
      letI := hfinite
      let q := nativeOriginalPointGeometricLift ep (toBase I) b v hv
      let F := nativeOriginalBaseChangeMap f (toBase I) b
      finiteSchemeRank c = Nat.card
        {y : ↥(pullback (f ≫ toBase I) b : Scheme.{u}) | F y = q (IsLocalRing.closedPoint Ω)} := by
  letI := pointAlgebra (toBase I) P.1
  let ep := (scheme I).fromSpecResidueField P.1
  let f := coefficientComponentToOriginal I D hID
  let c := pullback.fst ep f
  let b := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
  let v := Spec.map (CommRingCat.ofHom psi.toRingHom)
  let t := pullback.snd c v
  letI : IsFinite f := (coefficientComponentToOriginal_finite_and_toBase I D hID).1
  letI : FormallyUnramified f := coefficientComponentToOriginal_formallyUnramified I D hID
  letI : IsFinite c := by dsimp only [c]; infer_instance
  letI : FormallyUnramified c :=
    MorphismProperty.pullback_fst (P := @FormallyUnramified.{u}) ep f inferInstance
  letI : IsFinite t := by dsimp only [t]; infer_instance
  letI : FormallyUnramified t :=
    MorphismProperty.pullback_snd (P := @FormallyUnramified.{u}) c v inferInstance
  obtain ⟨hv, _hsection, _hP⟩ := originalPointModelIncidence_residueEmbedding_geometricLift I P psi
  obtain ⟨_hclosed, e, _he⟩ := nativeEntireIncidence_originalBaseChange_supportEquiv
    ep f (toBase I) b v hv
  refine ⟨inferInstance, hv, ?_⟩
  calc
    finiteSchemeRank c = finiteSchemeRank t :=
      finiteSchemeRank_eq_of_field_baseChange c v t (Iso.refl _) (by simp [t])
    _ = Nat.card ↥(pullback c v : Scheme.{u}) := finiteFormallyUnramifiedScheme_overAlgClosed_rank_eq_carrierCard t
    _ = _ := Nat.card_congr e

end PfaffianDescent.Coray
