import PfaffianDescent.ResidualAffineScheme
import PfaffianDescent.FiniteSchemeResidual
import PfaffianDescent.FiniteEtaleSchemeFrobenius
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation

/-!
# Complementarity of residual ideals in finite étale algebras

The annihilator residual of an ideal in a reduced finite algebra is supported
on the complementary set of field factors.  Algebraically, the original ideal
and its residual annihilator are comaximal.  This is the ring-theoretic input
for the disjoint degree-three-plus-degree-eight fiber in Voisin's rank-two
construction.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory Module

section Semisimple

variable {A : Type*} [CommRing A] [IsSemisimpleRing A]

/-- In a semisimple commutative algebra, an ideal and its annihilator generate
`⊤`. -/
theorem ideal_sup_residualAlgebraIdeal_eq_top_of_semisimple (P : Ideal A) :
    P ⊔ residualAlgebraIdeal P = ⊤ := by
  obtain ⟨e, he, hP⟩ := IsSemisimpleRing.ideal_eq_span_idempotent P
  apply (Ideal.eq_top_iff_one _).mpr
  rw [Submodule.mem_sup]
  refine ⟨e, ?_, 1 - e, ?_, by ring⟩
  · rw [hP]
    exact Ideal.subset_span (Set.mem_singleton e)
  · rw [hP]
    rw [Submodule.mem_annihilator_span_singleton]
    change (1 - e) * e = 0
    rw [sub_mul, one_mul, he.eq]
    ring

omit [IsSemisimpleRing A] in
/-- The annihilator residual of an idempotent component is its complementary
idempotent component. -/
theorem residualAlgebraIdeal_span_idempotent (e : A) (he : e * e = e) :
    residualAlgebraIdeal (Ideal.span ({e} : Set A)) =
      Ideal.span ({1 - e} : Set A) := by
  ext x
  rw [residualAlgebraIdeal, Submodule.mem_annihilator_span_singleton]
  change x * e = 0 ↔ x ∈ Ideal.span ({1 - e} : Set A)
  constructor
  · intro hx
    rw [Ideal.mem_span_singleton]
    refine ⟨x, ?_⟩
    calc
      x = x * 1 := (mul_one x).symm
      _ = x * e + x * (1 - e) := by ring
      _ = x * (1 - e) := by rw [hx, zero_add]
      _ = (1 - e) * x := by ring
  · rw [Ideal.mem_span_singleton]
    rintro ⟨a, rfl⟩
    have hcomp : (1 - e) * e = 0 := by
      rw [sub_mul, one_mul, he, sub_self]
    calc
      ((1 - e) * a) * e = ((1 - e) * e) * a := by ring
      _ = 0 := by rw [hcomp, zero_mul]

/-- On a semisimple commutative algebra, the annihilator residual operation
is involutive.  Thus the original closed component and its residual are
genuine complementary factors, not merely disjoint subschemes. -/
theorem residualAlgebraIdeal_residualAlgebraIdeal_eq (P : Ideal A) :
    residualAlgebraIdeal (residualAlgebraIdeal P) = P := by
  obtain ⟨e, he, hP⟩ := IsSemisimpleRing.ideal_eq_span_idempotent P
  rw [hP, residualAlgebraIdeal_span_idempotent e he.eq]
  have hcomp : (1 - e) * (1 - e) = 1 - e := by
    calc
      (1 - e) * (1 - e) = 1 - (e + e) + e * e := by ring
      _ = 1 - e := by rw [he.eq]; ring
  rw [residualAlgebraIdeal_span_idempotent (1 - e) hcomp]
  simp only [sub_sub_cancel]

/-- In a semisimple commutative algebra, a component and its annihilator
residual have zero intersection.  Together with their comaximality this says
that they are actual complementary factors. -/
theorem inf_residualAlgebraIdeal_eq_bot_of_semisimple (P : Ideal A) :
    P ⊓ residualAlgebraIdeal P = ⊥ := by
  obtain ⟨e, he, hP⟩ := IsSemisimpleRing.ideal_eq_span_idempotent P
  rw [hP, residualAlgebraIdeal_span_idempotent e he.eq]
  apply le_bot_iff.mp
  intro x hx
  rw [Submodule.mem_inf] at hx
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hx.1
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hx.2
  rw [Submodule.mem_bot]
  calc
    x = e * a := ha
    _ = (e * e) * a := by rw [he.eq]
    _ = e * (e * a) := by rw [mul_assoc]
    _ = e * x := by rw [← ha]
    _ = e * ((1 - e) * b) := by rw [hb]
    _ = (e * (1 - e)) * b := by rw [mul_assoc]
    _ = 0 := by rw [mul_sub, mul_one, he.eq, sub_self, zero_mul]

/-- The original algebra is the product of the quotient by a component and
the quotient by its annihilator residual.  This is the Chinese-remainder
form of the finite étale residual decomposition. -/
noncomputable def residualAlgebraQuotientProdEquiv (P : Ideal A) :
    A ≃+* (A ⧸ P) × (A ⧸ residualAlgebraIdeal P) := by
  let hsup : P ⊔ residualAlgebraIdeal P = ⊤ :=
    ideal_sup_residualAlgebraIdeal_eq_top_of_semisimple P
  let hcop : IsCoprime P (residualAlgebraIdeal P) :=
    Ideal.isCoprime_iff_sup_eq.mpr hsup
  let hinf : P ⊓ residualAlgebraIdeal P = ⊥ :=
    inf_residualAlgebraIdeal_eq_bot_of_semisimple P
  exact (RingEquiv.quotientBot A).symm.trans
    ((Ideal.quotEquivOfEq hinf.symm).trans
      (Ideal.quotientInfEquivQuotientProd P (residualAlgebraIdeal P) hcop))

/-- The first projection of the residual product equivalence is the ordinary
quotient map. -/
@[simp]
theorem residualAlgebraQuotientProdEquiv_fst (P : Ideal A) (x : A) :
    (residualAlgebraQuotientProdEquiv P x).1 = Ideal.Quotient.mk P x := by
  unfold residualAlgebraQuotientProdEquiv
  simp only [RingEquiv.trans_apply, RingEquiv.quotientBot_symm_mk]
  rw [Ideal.quotEquivOfEq_mk]
  rw [Ideal.quotientInfEquivQuotientProd_fst]
  rfl

/-- The second projection of the residual product equivalence is the
annihilator-residual quotient map. -/
@[simp]
theorem residualAlgebraQuotientProdEquiv_snd (P : Ideal A) (x : A) :
    (residualAlgebraQuotientProdEquiv P x).2 =
      Ideal.Quotient.mk (residualAlgebraIdeal P) x := by
  unfold residualAlgebraQuotientProdEquiv
  simp only [RingEquiv.trans_apply, RingEquiv.quotientBot_symm_mk]
  rw [Ideal.quotEquivOfEq_mk]
  rw [Ideal.quotientInfEquivQuotientProd_snd]
  rfl

end Semisimple


section Affine

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A] [Module.Finite K A]

/-- The two quotient maps defined by comaximal ideals have disjoint images on
prime spectra. -/
theorem disjoint_range_quotientAffineι_residualAffineι_of_sup_eq_top
    (P : Ideal A) (hP : P ⊔ residualAlgebraIdeal P = ⊤) :
    Disjoint
      (Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk P))))
      (Set.range (residualAffineι P)) := by
  rw [Set.disjoint_left]
  rintro x ⟨y, hy⟩ ⟨z, hz⟩
  rw [Spec.map_apply] at hy
  change (Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.mk (residualAlgebraIdeal P)))) z = x at hz
  rw [Spec.map_apply] at hz
  let y' : PrimeSpectrum (A ⧸ P) := y
  let z' : PrimeSpectrum (A ⧸ residualAlgebraIdeal P) := z
  have hy' : PrimeSpectrum.comap (Ideal.Quotient.mk P) y' = x := hy
  have hz' : PrimeSpectrum.comap (Ideal.Quotient.mk (residualAlgebraIdeal P)) z' = x := hz
  have heq : PrimeSpectrum.comap (Ideal.Quotient.mk P) y' =
      PrimeSpectrum.comap (Ideal.Quotient.mk (residualAlgebraIdeal P)) z' :=
    hy'.trans hz'.symm
  have hleft : P ≤ (PrimeSpectrum.comap (Ideal.Quotient.mk P) y').asIdeal := by
    rw [PrimeSpectrum.comap_asIdeal]
    exact (Ideal.mk_ker (I := P)).symm.trans_le (Ideal.ker_le_comap _)
  have hright : residualAlgebraIdeal P ≤
      (PrimeSpectrum.comap (Ideal.Quotient.mk P) y').asIdeal := by
    rw [heq, PrimeSpectrum.comap_asIdeal]
    exact (Ideal.mk_ker (I := residualAlgebraIdeal P)).symm.trans_le
      (Ideal.ker_le_comap _)
  have htop : (⊤ : Ideal A) ≤
      (PrimeSpectrum.comap (Ideal.Quotient.mk P) y').asIdeal := by
    rw [← hP]
    exact sup_le hleft hright
  exact (PrimeSpectrum.comap (Ideal.Quotient.mk P) y').isPrime.ne_top
    (top_unique htop)

end Affine

section FiniteEtaleQuotient

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]
  [Algebra.Etale K A] [Module.Finite K A]

/-- A quotient of a finite étale algebra over a field is finite étale.

For the finite residual construction, this is the algebraic reason that a
closed complementary subscheme of a finite étale scheme is again étale.  The
field hypothesis turns formal unramifiedness of the quotient into formal
étaleness, while finite dimensionality supplies finite presentation. -/
theorem quotient_algebraEtale_of_field (I : Ideal A) :
    letI : Algebra K (A ⧸ I) := Ideal.Quotient.algebra K
    Algebra.Etale K (A ⧸ I) := by
  letI : Algebra K (A ⧸ I) := Ideal.Quotient.algebra K
  letI : Algebra.FormallyEtale K (A ⧸ I) :=
    Algebra.FormallyEtale.of_formallyUnramified_of_field K (A ⧸ I)
  letI : Module.Finite K (A ⧸ I) := Module.Finite.quotient K I
  letI : Module.FinitePresentation K (A ⧸ I) :=
    Module.finitePresentation_of_finite K (A ⧸ I)
  letI : Algebra.FinitePresentation K (A ⧸ I) :=
    Algebra.FinitePresentation.of_finitePresentation K (A ⧸ I)
  exact { formallyEtale := inferInstance, finitePresentation := inferInstance }

end FiniteEtaleQuotient

section FiniteReduced

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]
  [Module.Finite K A] [IsReduced A]

include K

/-- A finite reduced algebra over a field is semisimple, so every ideal is
comaximal with its annihilator residual. -/
theorem ideal_sup_residualAlgebraIdeal_eq_top_of_finiteReduced (P : Ideal A) :
    P ⊔ residualAlgebraIdeal P = ⊤ := by
  let _ : IsArtinianRing A := isArtinian_of_tower K inferInstance
  let _ : IsSemisimpleRing A := IsArtinianRing.isSemisimpleRing_of_isReduced A
  exact ideal_sup_residualAlgebraIdeal_eq_top_of_semisimple P

/-- In a finite reduced algebra over a field, the quotient by an ideal and
its annihilator residual are disjoint closed affine subschemes. -/
theorem disjoint_range_quotientAffineι_residualAffineι_of_finiteReduced
    (P : Ideal A) :
    Disjoint
      (Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk P))))
      (Set.range (residualAffineι P)) := by
  exact disjoint_range_quotientAffineι_residualAffineι_of_sup_eq_top P
    (ideal_sup_residualAlgebraIdeal_eq_top_of_finiteReduced (K := K) P)

end FiniteReduced


section FiniteEtaleScheme

universe u

variable {K : Type u} [Field K] {X Z : Scheme.{u}}

/-- In a finite étale scheme over a field, the equations of any closed
subscheme are comaximal with the equations of its annihilator residual. -/
theorem finiteEtaleScheme_ker_sup_residualAlgebraIdeal_eq_top
    (i : Z ⟶ X) (f : X ⟶ Spec (.of K)) [IsFinite f] [Etale f] :
    RingHom.ker i.appTop.hom ⊔
      residualAlgebraIdeal (RingHom.ker i.appTop.hom) = ⊤ := by
  let _ : IsAffine X := isAffine_of_isAffineHom f
  let _ := finiteSchemeCoefficientAlgebra f
  have hfinite := finiteSchemeCoefficient_finite f
  have hspec : Etale
      (Spec.map (CommRingCat.ofHom (algebraMap K Γ(X, ⊤)))) := by
    rw [finiteSchemeCoefficient_spec f]
    infer_instance
  have hring : (algebraMap K Γ(X, ⊤)).Etale :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mp hspec
  let _ : Algebra.Etale K Γ(X, ⊤) := RingHom.etale_algebraMap.mp hring
  let _ : IsReduced Γ(X, ⊤) :=
    Algebra.FormallyUnramified.isReduced_of_field K Γ(X, ⊤)
  exact ideal_sup_residualAlgebraIdeal_eq_top_of_finiteReduced
    (K := K) (A := Γ(X, ⊤)) (RingHom.ker i.appTop.hom)

/-- In a finite étale scheme over a field, residualizing twice recovers the
original ideal of equations.  This is the scheme-level form of the
complementarity used in the rank-three/rank-eight decomposition. -/
theorem finiteEtaleScheme_residualAlgebraIdeal_involutive
    (i : Z ⟶ X) (f : X ⟶ Spec (.of K)) [IsFinite f] [Etale f] :
    residualAlgebraIdeal (residualAlgebraIdeal (RingHom.ker i.appTop.hom)) =
      RingHom.ker i.appTop.hom := by
  let _ : IsAffine X := isAffine_of_isAffineHom f
  let _ := finiteSchemeCoefficientAlgebra f
  have hfinite := finiteSchemeCoefficient_finite f
  have hspec : Etale
      (Spec.map (CommRingCat.ofHom (algebraMap K Γ(X, ⊤)))) := by
    rw [finiteSchemeCoefficient_spec f]
    infer_instance
  have hring : (algebraMap K Γ(X, ⊤)).Etale :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mp hspec
  let _ : Algebra.Etale K Γ(X, ⊤) := RingHom.etale_algebraMap.mp hring
  let _ : IsReduced Γ(X, ⊤) :=
    Algebra.FormallyUnramified.isReduced_of_field K Γ(X, ⊤)
  let _ : IsArtinianRing Γ(X, ⊤) := isArtinian_of_tower K inferInstance
  let _ : IsSemisimpleRing Γ(X, ⊤) :=
    IsArtinianRing.isSemisimpleRing_of_isReduced Γ(X, ⊤)
  exact residualAlgebraIdeal_residualAlgebraIdeal_eq _

/-- A finite étale scheme splits as the coproduct of the spectra of the two
complementary quotient algebras defined by a closed component and its
annihilator residual. -/
noncomputable def finiteEtaleScheme_residualCoproductIso
    (i : Z ⟶ X) (f : X ⟶ Spec (.of K)) [IsFinite f] [Etale f] :
    X ≅ Spec (.of (Γ(X, ⊤) ⧸ RingHom.ker i.appTop.hom)) ⨿
      Spec (.of (Γ(X, ⊤) ⧸ residualAlgebraIdeal (RingHom.ker i.appTop.hom))) := by
  let _ : IsAffine X := isAffine_of_isAffineHom f
  let _ := finiteSchemeCoefficientAlgebra f
  have hfinite := finiteSchemeCoefficient_finite f
  have hspec : Etale
      (Spec.map (CommRingCat.ofHom (algebraMap K Γ(X, ⊤)))) := by
    rw [finiteSchemeCoefficient_spec f]
    infer_instance
  have hring : (algebraMap K Γ(X, ⊤)).Etale :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mp hspec
  let _ : Algebra.Etale K Γ(X, ⊤) := RingHom.etale_algebraMap.mp hring
  let _ : IsReduced Γ(X, ⊤) :=
    Algebra.FormallyUnramified.isReduced_of_field K Γ(X, ⊤)
  let _ : IsArtinianRing Γ(X, ⊤) := isArtinian_of_tower K inferInstance
  let _ : IsSemisimpleRing Γ(X, ⊤) :=
    IsArtinianRing.isSemisimpleRing_of_isReduced Γ(X, ⊤)
  let P := RingHom.ker i.appTop.hom
  let e := residualAlgebraQuotientProdEquiv P
  let e' := e.toCommRingCatIso
  let q := asIso (Spec.map e'.hom)
  let c := asIso (coprodSpec (Γ(X, ⊤) ⧸ P)
    (Γ(X, ⊤) ⧸ residualAlgebraIdeal P))
  exact X.isoSpec ≪≫ q.symm ≪≫ c.symm

/-- If the chosen component is a closed immersion, the preceding product
decomposition identifies the finite étale scheme itself with that component
and its annihilator residual. -/
noncomputable def finiteEtaleScheme_componentResidualCoproductIso
    (i : Z ⟶ X) [IsClosedImmersion i]
    (f : X ⟶ Spec (.of K)) [IsFinite f] [Etale f] :
    X ≅ Z ⨿ Spec (.of
      (Γ(X, ⊤) ⧸ residualAlgebraIdeal (RingHom.ker i.appTop.hom))) := by
  let _ : IsAffine X := isAffine_of_isAffineHom f
  let _ : IsAffine Z := isAffine_of_isAffineHom i
  have hi : Function.Surjective i.appTop.hom :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine i).2
  let q := RingHom.quotientKerEquivOfSurjective hi
  let q' := q.toCommRingCatIso
  let a := Z.isoSpec ≪≫ asIso (Spec.map q'.hom)
  let b := finiteEtaleScheme_residualCoproductIso i f
  exact b ≪≫ (CategoryTheory.Limits.coprod.mapIso a (Iso.refl _)).symm

/-- An annihilator residual inside a finite étale scheme over a field is again
étale over the field.  On global functions it is a quotient of a finite étale
algebra; quotients preserve formal unramifiedness, and finite dimensionality
over the field supplies the finite-presentation part of étaleness. -/
theorem finiteClosedResidual_toBase_etale
    (i : Z ⟶ X) (f : X ⟶ Spec (.of K)) [IsFinite f] [Etale f] :
    Etale (finiteClosedResidualι i f ≫ f) := by
  let _ : IsAffine X := isAffine_of_isAffineHom f
  let _ := finiteSchemeCoefficientAlgebra f
  have hfinite := finiteSchemeCoefficient_finite f
  have hspec : Etale
      (Spec.map (CommRingCat.ofHom (algebraMap K Γ(X, ⊤)))) := by
    rw [finiteSchemeCoefficient_spec f]
    infer_instance
  have hring : (algebraMap K Γ(X, ⊤)).Etale :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mp hspec
  let _ : Algebra.Etale K Γ(X, ⊤) := RingHom.etale_algebraMap.mp hring
  let P := RingHom.ker i.appTop.hom
  letI : Algebra.Etale K (Γ(X, ⊤) ⧸ residualAlgebraIdeal P) :=
    quotient_algebraEtale_of_field (residualAlgebraIdeal P)
  have hcomp : finiteClosedResidualι i f ≫ f =
      residualAffineι P ≫ Spec.map (CommRingCat.ofHom (algebraMap K Γ(X, ⊤))) := by
    rw [finiteSchemeCoefficient_spec f]
    exact Category.assoc _ _ _
  rw [hcomp, residualAffineι_toBase]
  apply (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
  exact RingHom.etale_algebraMap.mpr inferInstance

/-- In a finite étale scheme, the annihilator residual to a closed subscheme
remains finite étale and has the complementary rank. This bundles the two
properties used by each finite residual step in Voisin's construction. -/
theorem finiteClosedResidual_rank_complement_and_etale_of_finiteEtale
    (i : Z ⟶ X) [IsClosedImmersion i]
    (f : X ⟶ Spec (.of K)) [CharZero K] [IsFinite f] [Etale f]
    (N d : ℕ) (hX : AllCharacteristics.finiteSchemeRank f = N)
    (hZ : AllCharacteristics.finiteSchemeRank (i ≫ f) = d) :
    Etale (finiteClosedResidualι i f ≫ f) ∧
      AllCharacteristics.finiteSchemeRank (finiteClosedResidualι i f ≫ f) = N - d := by
  refine ⟨finiteClosedResidual_toBase_etale i f, ?_⟩
  exact finite_scheme_residual_rank_complement i f N d hX hZ
    (finiteEtaleScheme_exists_frobeniusFunctional f)

/-- The ambient-scheme form of the finite étale residual calculation. It is
the form needed after realizing the rank-sixteen datum inside the finite
three-cubic intersection: the residual maps back to the original cubic and
is still finite étale of complementary rank. -/
theorem finiteClosedResidualOnAmbient_rank_complement_and_etale_of_finiteEtale
    {Y : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i]
    (c : X ⟶ Y) (f : Y ⟶ Spec (.of K))
    [CharZero K] [IsFinite (c ≫ f)] [Etale (c ≫ f)]
    (N d : ℕ) (hX : AllCharacteristics.finiteSchemeRank (c ≫ f) = N)
    (hZ : AllCharacteristics.finiteSchemeRank (i ≫ c ≫ f) = d) :
    letI : IsFinite ((finiteClosedResidualι i (c ≫ f) ≫ c) ≫ f) := by
      rw [Category.assoc]
      infer_instance
    Etale ((finiteClosedResidualι i (c ≫ f) ≫ c) ≫ f) ∧
      AllCharacteristics.finiteSchemeRank
        ((finiteClosedResidualι i (c ≫ f) ≫ c) ≫ f) = N - d := by
  letI : IsFinite ((finiteClosedResidualι i (c ≫ f) ≫ c) ≫ f) := by
    rw [Category.assoc]
    infer_instance
  have h := finiteClosedResidual_rank_complement_and_etale_of_finiteEtale
    i (c ≫ f) N d hX (by simpa only [Category.assoc] using hZ)
  simpa only [Category.assoc] using h

end FiniteEtaleScheme


section ClosedImmersionRange

variable {X Z : Scheme.{u}}

/-- An affine closed immersion has the same set-theoretic image as the
quotient by the kernel of its map on global functions. -/
theorem range_closedImmersion_eq_range_quotientAffine [IsAffine X]
    (i : Z ⟶ X) [IsClosedImmersion i] :
    Set.range i = Set.range
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker i.appTop.hom))) ≫
        X.isoSpec.inv) := by
  let _ : IsAffine Z := isAffine_of_isAffineHom i
  have hi : Function.Surjective i.appTop.hom :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine i).2
  let e := RingHom.quotientKerEquivOfSurjective hi
  let E := e.toCommRingCatIso
  have hq : CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker i.appTop.hom)) =
      i.appTop ≫ E.inv := by
    ext a
    change Ideal.Quotient.mk _ a = e.symm (i.appTop a)
    simp [e]
  have hmap :
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker i.appTop.hom))) ≫
        X.isoSpec.inv =
      Spec.map E.inv ≫ Z.isoSpec.inv ≫ i := by
    rw [hq, Spec.map_comp]
    calc
      Spec.map E.inv ≫ Spec.map i.appTop ≫
          X.isoSpec.inv =
          Spec.map E.inv ≫
            (Spec.map i.appTop ≫ X.isoSpec.inv) := (Category.assoc _ _ _).symm
      _ = Spec.map E.inv ≫
            (Z.isoSpec.inv ≫ i) := by rw [Scheme.isoSpec_inv_naturality]
      _ = Spec.map E.inv ≫ Z.isoSpec.inv ≫ i := rfl
  let p := Spec.map E.inv ≫ Z.isoSpec.inv
  have hp : Function.Surjective p := by
    let q := Spec.map E.inv
    let _ : IsIso q := by
      dsimp [q]
      infer_instance
    intro z
    refine ⟨(Z.isoSpec.hom ≫ inv q) z, ?_⟩
    have hright : (Z.isoSpec.hom ≫ inv q) ≫ p = 𝟙 Z := by
      dsimp [p]
      simp [q, Category.assoc]
    exact congrArg (fun g => g z) hright
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨w, hw⟩ := hp z
    refine ⟨w, ?_⟩
    rw [hmap]
    change i (p w) = i z
    rw [hw]
  · rintro ⟨w, hw⟩
    rw [hmap] at hw
    exact ⟨p w, hw⟩

end ClosedImmersionRange


section FiniteEtaleSchemeDisjoint

variable {K : Type u} [Field K] {X Z : Scheme.{u}}

/-- In a finite étale scheme over a field, a closed subscheme and its
annihilator residual have disjoint underlying supports. -/
theorem disjoint_range_closedImmersion_finiteClosedResidualι_of_finiteEtale
    (i : Z ⟶ X) (f : X ⟶ Spec (.of K)) [IsFinite f] [Etale f]
    [IsClosedImmersion i] :
    Disjoint (Set.range i) (Set.range (finiteClosedResidualι i f)) := by
  let _ : IsAffine X := isAffine_of_isAffineHom f
  let _ := finiteSchemeCoefficientAlgebra f
  have hfinite := finiteSchemeCoefficient_finite f
  let P := RingHom.ker i.appTop.hom
  have htop : P ⊔ residualAlgebraIdeal P = ⊤ :=
    finiteEtaleScheme_ker_sup_residualAlgebraIdeal_eq_top i f
  have hraw : Disjoint
      (Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk P))))
      (Set.range (residualAffineι P)) :=
    disjoint_range_quotientAffineι_residualAffineι_of_sup_eq_top P htop
  have horig : Set.range i = Set.range
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk P)) ≫ X.isoSpec.inv) := by
    simpa [P] using range_closedImmersion_eq_range_quotientAffine i
  unfold finiteClosedResidualι
  rw [horig, Set.disjoint_left]
  rintro x ⟨y, hy⟩ ⟨z, hz⟩
  have hinj : Function.Injective X.isoSpec.inv := by
    intro a b hab
    have h := congrArg (fun g => X.isoSpec.hom g) hab
    simpa using h
  apply (Set.disjoint_left.mp hraw)
  · exact ⟨y, rfl⟩
  · refine ⟨z, ?_⟩
    apply hinj
    exact hz.trans hy.symm

end FiniteEtaleSchemeDisjoint

end PfaffianDescent
