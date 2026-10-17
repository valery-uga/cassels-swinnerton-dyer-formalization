import PfaffianDescent.VoisinGaloisOrbitLocus
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.Artinian.Module
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-!
# Geometric conjugates after scalar extension

Voisin's Galois orbit consists of distinct geometric points on the
scalar-extended surface.  This file constructs those points on the actual
scheme-theoretic base change.  It replaces the useful but topologically
collapsed map `galoisEmbeddingPoint`, whose values all lie at the single
closed point on the original scheme.
-/

namespace PfaffianDescent

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

universe u

section

variable {K A L : Type u} [Field K] [Field A] [Algebra K A]
    [Field L] [Algebra K L]

/-- The scalar extension of a `K`-scheme to `L`. -/
noncomputable abbrev schemeBaseChangeToField
    (X : Scheme.{u}) (p : X ⟶ Spec (.of K)) : Scheme.{u} :=
  pullback p (Spec.map (CommRingCat.ofHom (algebraMap K L)))

/-- Evaluation of the split fibre algebra `A ⊗[K] L` at a `K`-embedding
`A → L`. -/
noncomputable def embeddingTensorEval (phi : A →ₐ[K] L) :
    A ⊗[K] L →ₐ[K] L :=
  Algebra.TensorProduct.productMap phi (AlgHom.id K L)

/-- Evaluation on the tensor order `L ⊗[K] A` used by the affine pullback
model. -/
noncomputable def baseChangeEmbeddingEval (phi : A →ₐ[K] L) :
    L ⊗[K] A →ₐ[L] L :=
  Algebra.TensorProduct.liftEquivRight K L A L phi

@[simp]
theorem baseChangeEmbeddingEval_tmul (phi : A →ₐ[K] L) (l : L) (a : A) :
    baseChangeEmbeddingEval phi (l ⊗ₜ[K] a) = l * phi a := rfl

@[simp]
theorem embeddingTensorEval_tmul (phi : A →ₐ[K] L) (a : A) (l : L) :
    embeddingTensorEval phi (a ⊗ₜ[K] l) = phi a * l := rfl

/-- The prime of `A ⊗[K] L` cut out by evaluation at an embedding. -/
noncomputable def embeddingTensorPoint (phi : A →ₐ[K] L) :
    PrimeSpectrum (A ⊗[K] L) :=
  PrimeSpectrum.comap (embeddingTensorEval phi).toRingHom (specClosedPoint L)

theorem embeddingTensorPoint_asIdeal (phi : A →ₐ[K] L) :
    (embeddingTensorPoint phi).asIdeal = RingHom.ker (embeddingTensorEval phi) := by
  change Ideal.comap (embeddingTensorEval phi).toRingHom
      (IsLocalRing.maximalIdeal L) = _
  rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot]
  exact RingHom.ker_coe_toRingHom (f := embeddingTensorEval phi)

/-- Different embeddings cut out different points of the scalar-extended
finite fibre.  The separating tensor is
`a ⊗ 1 - 1 ⊗ phi(a)`. -/
theorem embeddingTensorPoint_injective :
    Function.Injective (embeddingTensorPoint (K := K) (A := A) (L := L)) := by
  intro phi psi hpoint
  by_contra hne
  have hex : ∃ a : A, phi a ≠ psi a := by
    by_contra h
    push Not at h
    exact hne (AlgHom.ext h)
  obtain ⟨a, ha⟩ := hex
  let t : A ⊗[K] L := a ⊗ₜ[K] 1 - 1 ⊗ₜ[K] phi a
  have htphi : t ∈ (embeddingTensorPoint phi).asIdeal := by
    rw [embeddingTensorPoint_asIdeal]
    change embeddingTensorEval phi t = 0
    simp [t, embeddingTensorEval]
  have htpsi : t ∉ (embeddingTensorPoint psi).asIdeal := by
    rw [embeddingTensorPoint_asIdeal]
    change embeddingTensorEval psi t ≠ 0
    simpa [t, embeddingTensorEval, sub_eq_zero] using ha.symm
  rw [hpoint] at htphi
  exact htpsi htphi

set_option linter.style.haveILetI false in
/-- Embeddings of the residue field into a separably closed extension are
exactly the geometric points of the scalar-extended finite fibre. -/
noncomputable def finiteSeparableEmbeddingEquivPrimeSpectrum
    [FiniteDimensional K A] [Algebra.IsSeparable K A] [IsSepClosed L] :
    (A →ₐ[K] L) ≃ PrimeSpectrum (L ⊗[K] A) := by
  letI : Algebra.FormallyEtale K A := Algebra.FormallyEtale.of_isSeparable K A
  exact (Algebra.TensorProduct.liftEquivRight K L A L).trans
    (Algebra.IsFiniteSplit.algHomEquivPrimeSpectrum L (L ⊗[K] A))

theorem finiteSeparableEmbeddingEquivPrimeSpectrum_asIdeal
    [FiniteDimensional K A] [Algebra.IsSeparable K A] [IsSepClosed L]
    (phi : A →ₐ[K] L) :
    ((finiteSeparableEmbeddingEquivPrimeSpectrum
      (K := K) (A := A) (L := L)) phi).asIdeal =
      RingHom.ker (baseChangeEmbeddingEval phi) := by
  letI : Algebra.FormallyEtale K A := Algebra.FormallyEtale.of_isSeparable K A
  exact Algebra.IsFiniteSplit.coe_algHomEquivPrimeSpectrum
    (baseChangeEmbeddingEval phi)

set_option linter.style.haveILetI false in
/-- A finite separable field point becomes a finite product of copies of the
separably closed extension field after scalar extension.  The factors are
indexed by the actual points of the split fibre. -/
noncomputable def finiteSeparableBaseChangeEquivPi
    [FiniteDimensional K A] [Algebra.IsSeparable K A] [IsSepClosed L] :
    (L ⊗[K] A) ≃ₐ[L] (∀ _ : PrimeSpectrum (L ⊗[K] A), L) := by
  letI : Algebra.FormallyEtale K A := Algebra.FormallyEtale.of_isSeparable K A
  exact Algebra.FormallyEtale.equivPiOfIsSepClosed L (L ⊗[K] A)

set_option linter.style.haveILetI false in
/-- At the split-fibre point indexed by an embedding, the product
decomposition's coordinate is the corresponding tensor-product evaluation. -/
theorem finiteSeparableBaseChangeEquivPi_apply_embedding
    [FiniteDimensional K A] [Algebra.IsSeparable K A] [IsSepClosed L]
    (phi : A →ₐ[K] L) (x : L ⊗[K] A) :
    finiteSeparableBaseChangeEquivPi (K := K) (A := A) (L := L) x
        (finiteSeparableEmbeddingEquivPrimeSpectrum
          (K := K) (A := A) (L := L) phi) =
      baseChangeEmbeddingEval phi x := by
  letI : Algebra.FormallyEtale K A := Algebra.FormallyEtale.of_isSeparable K A
  let q : PrimeSpectrum L := specClosedPoint L
  have hp :
      finiteSeparableEmbeddingEquivPrimeSpectrum
          (K := K) (A := A) (L := L) phi =
        PrimeSpectrum.comap (baseChangeEmbeddingEval phi).toRingHom q := by
    ext y
    rw [finiteSeparableEmbeddingEquivPrimeSpectrum_asIdeal]
    change y ∈ RingHom.ker (baseChangeEmbeddingEval phi) ↔
      y ∈ Ideal.comap (baseChangeEmbeddingEval phi).toRingHom
        (IsLocalRing.maximalIdeal L)
    rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot]
    rfl
  rw [hp]
  exact (Algebra.FormallyEtale.equivPiOfIsSepClosed_comap
    (baseChangeEmbeddingEval phi) x q).trans
      (Algebra.FormallyEtale.equivPiOfIsSepClosed_self_apply
        (baseChangeEmbeddingEval phi x) q)

set_option linter.style.haveILetI false in
/-- Affine product model for the scalar extension of a finite separable
field point.  This is the intermediate model underlying the coproduct
description below. -/
noncomputable def finiteSeparablePointBaseChangeIsoProduct
    [FiniteDimensional K A] [Algebra.IsSeparable K A] [IsSepClosed L] :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap K A)))
        (Spec.map (CommRingCat.ofHom (algebraMap K L))) ≅
      Spec (.of (∀ _ : PrimeSpectrum (L ⊗[K] A), L)) := by
  letI : Algebra.FormallyEtale K A := Algebra.FormallyEtale.of_isSeparable K A
  exact pullbackSymmetry _ _ ≪≫
    pullbackSpecIso K L A ≪≫
    AlgebraicGeometry.Scheme.Spec.mapIso
      (finiteSeparableBaseChangeEquivPi
        (K := K) (A := A) (L := L)).toRingEquiv.toCommRingCatIso.symm.op

set_option linter.style.haveILetI false in
/-- The coordinate point selected by an embedding, transported back through
the product-ring isomorphism, is the affine point defined by tensor
evaluation at that embedding. -/
theorem finiteSeparableProductCoordinate_toTensor
    [FiniteDimensional K A] [Algebra.IsSeparable K A] [IsSepClosed L]
    (phi : A →ₐ[K] L) :
    Spec.map (CommRingCat.ofHom
        (Pi.evalRingHom
          (fun _ : PrimeSpectrum (L ⊗[K] A) ↦ L)
          (finiteSeparableEmbeddingEquivPrimeSpectrum
            (K := K) (A := A) (L := L) phi))) ≫
      (AlgebraicGeometry.Scheme.Spec.mapIso
        (finiteSeparableBaseChangeEquivPi
          (K := K) (A := A) (L := L)).toRingEquiv.toCommRingCatIso.symm.op).inv =
    Spec.map (CommRingCat.ofHom (baseChangeEmbeddingEval phi).toRingHom) := by
  letI : Algebra.FormallyEtale K A := Algebra.FormallyEtale.of_isSeparable K A
  simp only [Functor.mapIso_inv, Iso.op_inv, Scheme.Spec_map,
    ← Spec.map_comp]
  rw [Spec.map_inj]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  exact finiteSeparableBaseChangeEquivPi_apply_embedding phi x

set_option linter.style.haveILetI false in
/-- Scheme-theoretically, the scalar extension of a finite separable field
point to a separably closed field is the finite coproduct of its geometric
points. -/
noncomputable def finiteSeparablePointBaseChangeIsoSigma
    [FiniteDimensional K A] [Algebra.IsSeparable K A] [IsSepClosed L] :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap K A)))
        (Spec.map (CommRingCat.ofHom (algebraMap K L))) ≅
      ∐ fun _ : PrimeSpectrum (L ⊗[K] A) ↦ Spec (.of L) := by
  letI : Algebra.FormallyEtale K A := Algebra.FormallyEtale.of_isSeparable K A
  letI : IsArtinianRing (L ⊗[K] A) := IsArtinianRing.of_finite L (L ⊗[K] A)
  letI : Fintype (PrimeSpectrum (L ⊗[K] A)) := Fintype.ofFinite _
  exact finiteSeparablePointBaseChangeIsoProduct
      (K := K) (A := A) (L := L) ≪≫
    (asIso (sigmaSpec
      (fun _ : PrimeSpectrum (L ⊗[K] A) ↦ CommRingCat.of L))).symm

/-- The base change of the finite point `Spec A ⟶ X`, mapped into the
scalar-extended ambient scheme. -/
noncomputable def finitePointBaseChangeToAmbient
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K))
    (center : Spec (.of A) ⟶ X)
    (hcenter : center ≫ p = Spec.map (CommRingCat.ofHom (algebraMap K A))) :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap K A)))
        (Spec.map (CommRingCat.ofHom (algebraMap K L))) ⟶
      schemeBaseChangeToField (L := L) X p := by
  apply pullback.map
    (Spec.map (CommRingCat.ofHom (algebraMap K A)))
    (Spec.map (CommRingCat.ofHom (algebraMap K L))) p
    (Spec.map (CommRingCat.ofHom (algebraMap K L)))
    center (𝟙 _) (𝟙 _)
  · simpa using hcenter.symm
  · simp

@[reassoc (attr := simp)]
theorem finitePointBaseChangeToAmbient_fst
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K))
    (center : Spec (.of A) ⟶ X)
    (hcenter : center ≫ p = Spec.map (CommRingCat.ofHom (algebraMap K A))) :
    finitePointBaseChangeToAmbient (L := L) p center hcenter ≫
        pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap K L))) =
      pullback.fst
        (Spec.map (CommRingCat.ofHom (algebraMap K A)))
        (Spec.map (CommRingCat.ofHom (algebraMap K L))) ≫ center := by
  unfold finitePointBaseChangeToAmbient
  exact pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem finitePointBaseChangeToAmbient_snd
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K))
    (center : Spec (.of A) ⟶ X)
    (hcenter : center ≫ p = Spec.map (CommRingCat.ofHom (algebraMap K A))) :
    finitePointBaseChangeToAmbient (L := L) p center hcenter ≫
        pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap K L))) =
      pullback.snd
        (Spec.map (CommRingCat.ofHom (algebraMap K A)))
        (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
  unfold finitePointBaseChangeToAmbient
  exact pullback.lift_snd _ _ _

/-- The square expressing `finitePointBaseChangeToAmbient` as the scalar
extension of the original point is cartesian. -/
theorem finitePointBaseChangeToAmbient_isPullback
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K))
    (center : Spec (.of A) ⟶ X)
    (hcenter : center ≫ p = Spec.map (CommRingCat.ofHom (algebraMap K A))) :
    IsPullback (finitePointBaseChangeToAmbient (L := L) p center hcenter)
      (pullback.fst
        (Spec.map (CommRingCat.ofHom (algebraMap K A)))
        (Spec.map (CommRingCat.ofHom (algebraMap K L))))
      (pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap K L)))) center := by
  let qA := Spec.map (CommRingCat.ofHom (algebraMap K A))
  let qL := Spec.map (CommRingCat.ofHom (algebraMap K L))
  let j := finitePointBaseChangeToAmbient (L := L) p center hcenter
  have hj : j ≫ pullback.fst p qL = pullback.fst qA qL ≫ center :=
    finitePointBaseChangeToAmbient_fst p center hcenter
  apply IsPullback.of_isLimit
    (c := PullbackCone.mk j (pullback.fst qA qL) hj)
  refine PullbackCone.IsLimit.mk hj
    (fun s => pullback.lift s.snd (s.fst ≫ pullback.snd p qL) ?_) ?_ ?_ ?_
  · calc
      s.snd ≫ qA = (s.snd ≫ center) ≫ p := by rw [Category.assoc, hcenter]
      _ = (s.fst ≫ pullback.fst p qL) ≫ p := by rw [s.condition]
      _ = (s.fst ≫ pullback.snd p qL) ≫ qL := by
        simp only [Category.assoc, pullback.condition]
  · intro s
    dsimp only [qA, qL]
    apply pullback.hom_ext (f := p) (g := qL)
    · calc
        (pullback.lift s.snd (s.fst ≫ pullback.snd p qL) _ ≫ j) ≫
              pullback.fst p qL =
            (pullback.lift s.snd (s.fst ≫ pullback.snd p qL) _ ≫
              pullback.fst qA qL) ≫ center := by
                rw [Category.assoc, hj, ← Category.assoc]
        _ = s.snd ≫ center := by rw [pullback.lift_fst]
        _ = s.fst ≫ pullback.fst p qL := s.condition.symm
    · calc
        (pullback.lift s.snd (s.fst ≫ pullback.snd p qL) _ ≫ j) ≫
              pullback.snd p qL =
            pullback.lift s.snd (s.fst ≫ pullback.snd p qL) _ ≫
              (j ≫ pullback.snd p qL) := Category.assoc _ _ _
        _ = pullback.lift s.snd (s.fst ≫ pullback.snd p qL) _ ≫
              pullback.snd qA qL := congrArg _
                (finitePointBaseChangeToAmbient_snd p center hcenter)
        _ = s.fst ≫ pullback.snd p qL := by rw [pullback.lift_snd]
  · intro s
    dsimp only [qA, qL]
    exact pullback.lift_fst _ _ _
  · intro s m hmj hmfst
    dsimp only [qA, qL] at hmj hmfst ⊢
    apply pullback.hom_ext
    · simpa only [pullback.lift_fst] using hmfst
    · rw [pullback.lift_snd]
      rw [← finitePointBaseChangeToAmbient_snd p center hcenter]
      simpa only [Category.assoc] using congrArg
        (fun k => k ≫ pullback.snd p qL) hmj

/-- Scalar extension preserves the closed immersion of the original finite
point into the ambient scheme. -/
noncomputable instance finitePointBaseChangeToAmbient_isClosedImmersion
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K))
    (center : Spec (.of A) ⟶ X) [IsClosedImmersion center]
    (hcenter : center ≫ p = Spec.map (CommRingCat.ofHom (algebraMap K A))) :
    IsClosedImmersion
      (finitePointBaseChangeToAmbient (L := L) p center hcenter) :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (finitePointBaseChangeToAmbient_isPullback
      (L := L) p center hcenter).flip inferInstance

/-- After the finite-separable splitting, the base-changed finite point is
displayed as an actual finite coproduct mapping to the scalar-extended
ambient scheme. -/
noncomputable def splitFinitePointToAmbient
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K))
    (center : Spec (.of A) ⟶ X)
    (hcenter : center ≫ p = Spec.map (CommRingCat.ofHom (algebraMap K A)))
    [FiniteDimensional K A] [Algebra.IsSeparable K A] [IsSepClosed L] :
    (∐ fun _ : PrimeSpectrum (L ⊗[K] A) ↦ Spec (.of L)) ⟶
      schemeBaseChangeToField (L := L) X p :=
  (finiteSeparablePointBaseChangeIsoSigma
      (K := K) (A := A) (L := L)).inv ≫
    finitePointBaseChangeToAmbient p center hcenter

/-- An embedding `A →ₐ[K] L` gives an `L`-valued geometric point on the
base change of `X`, provided the original `A`-point lies over `Spec K`. -/
noncomputable def galoisEmbeddingBaseChangeGeometricPoint
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K))
    (center : Spec (.of A) ⟶ X)
    (hcenter : center ≫ p = Spec.map (CommRingCat.ofHom (algebraMap K A)))
    (phi : A →ₐ[K] L) :
    Spec (.of L) ⟶ schemeBaseChangeToField (L := L) X p := by
  have w :
      (Spec.map (CommRingCat.ofHom phi.toRingHom) ≫ center) ≫ p =
        𝟙 (Spec (.of L)) ≫ Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
    rw [Category.assoc, hcenter, Category.id_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp]
    congr 2
    ext k
    exact phi.commutes k
  exact pullback.lift
    (Spec.map (CommRingCat.ofHom phi.toRingHom) ≫ center) (𝟙 _) w

/-- The underlying point of the scalar-extended surface determined by an
embedding of the residue field. -/
noncomputable def galoisEmbeddingBaseChangePoint
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K))
    (center : Spec (.of A) ⟶ X)
    (hcenter : center ≫ p = Spec.map (CommRingCat.ofHom (algebraMap K A))) :
    (A →ₐ[K] L) → schemeBaseChangeToField (L := L) X p := fun phi ↦
  galoisEmbeddingBaseChangeGeometricPoint p center hcenter phi (specClosedPoint L)

/-- The semilinear automorphism of a scalar-extended scheme induced by a
`K`-automorphism of the extension field. -/
noncomputable def schemeBaseChangeGaloisHom
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) (sigma : L ≃ₐ[K] L) :
    schemeBaseChangeToField (L := L) X p ⟶
      schemeBaseChangeToField (L := L) X p := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap K L))
  let s := Spec.map (CommRingCat.ofHom sigma.toRingHom)
  have hs : b ≫ 𝟙 (Spec (.of K)) = s ≫ b := by
    rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    unfold b
    rw [Spec.map_inj]
    ext k
    exact (sigma.commutes k).symm
  exact pullback.map p b p b (𝟙 X) s (𝟙 _) (by simp) hs

set_option linter.style.haveILetI false in
noncomputable instance schemeBaseChangeGaloisHom_isIso
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) (sigma : L ≃ₐ[K] L) :
    IsIso (schemeBaseChangeGaloisHom p sigma) := by
  letI : IsIso (CommRingCat.ofHom sigma.toRingHom) :=
    (ConcreteCategory.isIso_iff_bijective _).2 sigma.bijective
  unfold schemeBaseChangeGaloisHom
  dsimp only
  infer_instance

/-- The preceding semilinear endomorphism, packaged as an automorphism. -/
noncomputable def schemeBaseChangeGaloisIso
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) (sigma : L ≃ₐ[K] L) :
    schemeBaseChangeToField (L := L) X p ≅
      schemeBaseChangeToField (L := L) X p :=
  asIso (schemeBaseChangeGaloisHom p sigma)

@[reassoc (attr := simp)]
theorem schemeBaseChangeGaloisHom_fst
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) (sigma : L ≃ₐ[K] L) :
    schemeBaseChangeGaloisHom p sigma ≫
        pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap K L))) =
      pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
  unfold schemeBaseChangeGaloisHom
  exact pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem schemeBaseChangeGaloisHom_snd
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) (sigma : L ≃ₐ[K] L) :
    schemeBaseChangeGaloisHom p sigma ≫
        pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap K L))) =
      pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap K L))) ≫
        Spec.map (CommRingCat.ofHom sigma.toRingHom) := by
  unfold schemeBaseChangeGaloisHom
  exact pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
theorem galoisEmbeddingBaseChangeGeometricPoint_fst
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K))
    (center : Spec (.of A) ⟶ X)
    (hcenter : center ≫ p = Spec.map (CommRingCat.ofHom (algebraMap K A)))
    (phi : A →ₐ[K] L) :
    galoisEmbeddingBaseChangeGeometricPoint p center hcenter phi ≫
        pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap K L))) =
      Spec.map (CommRingCat.ofHom phi.toRingHom) ≫ center := by
  unfold galoisEmbeddingBaseChangeGeometricPoint
  exact pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem galoisEmbeddingBaseChangeGeometricPoint_snd
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K))
    (center : Spec (.of A) ⟶ X)
    (hcenter : center ≫ p = Spec.map (CommRingCat.ofHom (algebraMap K A)))
    (phi : A →ₐ[K] L) :
    galoisEmbeddingBaseChangeGeometricPoint p center hcenter phi ≫
        pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap K L))) = 𝟙 _ := by
  unfold galoisEmbeddingBaseChangeGeometricPoint
  exact pullback.lift_snd _ _ _

/-- The scalar-extension automorphisms carry the geometric point indexed by
`phi` to the point indexed by postcomposition with `sigma`.  The source point
is reparametrized by `sigma`, exactly as for semilinear Galois actions. -/
theorem galoisEmbeddingBaseChangeGeometricPoint_equivariant
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K))
    (center : Spec (.of A) ⟶ X)
    (hcenter : center ≫ p = Spec.map (CommRingCat.ofHom (algebraMap K A)))
    (sigma : L ≃ₐ[K] L) (phi : A →ₐ[K] L) :
    Spec.map (CommRingCat.ofHom sigma.toRingHom) ≫
        galoisEmbeddingBaseChangeGeometricPoint p center hcenter phi ≫
        schemeBaseChangeGaloisHom p sigma.symm =
      galoisEmbeddingBaseChangeGeometricPoint p center hcenter
        (sigma.toAlgHom.comp phi) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, schemeBaseChangeGaloisHom_fst,
      galoisEmbeddingBaseChangeGeometricPoint_fst]
    rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
    rfl
  · simp only [Category.assoc, schemeBaseChangeGaloisHom_snd,
      galoisEmbeddingBaseChangeGeometricPoint_snd_assoc,
      galoisEmbeddingBaseChangeGeometricPoint_snd]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id]
    rw [Spec.map_inj]
    ext l
    simp

/-- Equivariance on the underlying points of the scalar-extended surface. -/
theorem galoisEmbeddingBaseChangePoint_equivariant
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K))
    (center : Spec (.of A) ⟶ X)
    (hcenter : center ≫ p = Spec.map (CommRingCat.ofHom (algebraMap K A)))
    (sigma : L ≃ₐ[K] L) (phi : A →ₐ[K] L) :
    schemeBaseChangeGaloisHom p sigma.symm
        (galoisEmbeddingBaseChangePoint p center hcenter phi) =
      galoisEmbeddingBaseChangePoint p center hcenter
        (sigma.toAlgHom.comp phi) := by
  have h := congrArg (fun q : Spec (.of L) ⟶
      schemeBaseChangeToField (L := L) X p ↦ q (specClosedPoint L))
    (galoisEmbeddingBaseChangeGeometricPoint_equivariant
      p center hcenter sigma phi)
  have hs : Spec.map (CommRingCat.ofHom sigma.toRingHom) (specClosedPoint L) =
      specClosedPoint L := AlgebraicGeometry.Spec_closedPoint
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hs] at h
  simpa only [galoisEmbeddingBaseChangePoint, Scheme.Hom.comp_apply] using h

/-- Forgetting the scalar extension sends every conjugate geometric point to
the original degree-`[A:K]` closed point. -/
theorem galoisEmbeddingBaseChangePoint_fst
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K))
    (center : Spec (.of A) ⟶ X)
    (hcenter : center ≫ p = Spec.map (CommRingCat.ofHom (algebraMap K A)))
    (phi : A →ₐ[K] L) :
    pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap K L)))
        (galoisEmbeddingBaseChangePoint p center hcenter phi) =
      center (specClosedPoint A) := by
  change
    (galoisEmbeddingBaseChangeGeometricPoint p center hcenter phi ≫
      pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap K L))))
        (specClosedPoint L) = _
  rw [galoisEmbeddingBaseChangeGeometricPoint_fst]
  exact galoisEmbeddingPoint_eq_closedPoint (K := K) center phi

/-- Distinct field embeddings give distinct geometric-point morphisms on the
scalar extension.  This is the first separation property absent on the
original surface. -/
theorem galoisEmbeddingBaseChangeGeometricPoint_injective
    {X : Scheme.{u}} (p : X ⟶ Spec (.of K))
    (center : Spec (.of A) ⟶ X) [Mono center]
    (hcenter : center ≫ p = Spec.map (CommRingCat.ofHom (algebraMap K A))) :
    Function.Injective
      (galoisEmbeddingBaseChangeGeometricPoint (L := L) p center hcenter) := by
  intro phi psi h
  have hfst := congrArg
    (fun q ↦ q ≫ pullback.fst p
      (Spec.map (CommRingCat.ofHom (algebraMap K L)))) h
  rw [galoisEmbeddingBaseChangeGeometricPoint_fst,
    galoisEmbeddingBaseChangeGeometricPoint_fst] at hfst
  have hspec : Spec.map (CommRingCat.ofHom phi.toRingHom) =
      Spec.map (CommRingCat.ofHom psi.toRingHom) := by
    exact (cancel_mono center).mp hfst
  have hring : (CommRingCat.ofHom phi.toRingHom : CommRingCat.of A ⟶ CommRingCat.of L) =
      CommRingCat.ofHom psi.toRingHom :=
    Spec.map_injective hspec
  ext a
  exact ConcreteCategory.congr_hom hring a

end

end PfaffianDescent
