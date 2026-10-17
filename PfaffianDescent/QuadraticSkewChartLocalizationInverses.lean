import PfaffianDescent.QuadraticSkewHomogeneousChartEvaluationNaturality
/-! SOURCE ONLY / UNVERIFIED. Actual ordinary localizations for the inverse
preimage of the principal plane open. Both ring maps are constructed by
localization's universal property. The geometric caller derives the chart
identity from original-coordinate reconstruction; this module is only the
general ring-algebra step, and asserts no geometric rationality endpoint. -/

noncomputable section
namespace PfaffianDescent.QuadraticSkewRationality.SecondComposite005
universe u v w w'
variable {P : Type u} {C : Type v} {S : Type w} {T : Type w'}
variable [CommRing P] [CommRing C] [CommRing S] [CommRing T]
variable [Algebra P S] [Algebra C T]
variable (N : P) (θ : P →+* C) (φ : C →+* S)
variable [IsLocalization.Away N S] [IsLocalization.Away (θ N) T]
variable (hfirst : φ.comp θ = algebraMap P S)

theorem localizationLift_injective
    {D : Type*} [CommRing D] (f : C →+* D) (hf : Function.Injective f)
    (hunit : IsUnit (f (θ N))) :
    Function.Injective (IsLocalization.Away.lift (θ N) hunit : T →+* D) := by
  apply (IsLocalization.lift_injective_iff
    (show ∀ a : Submonoid.powers (θ N), IsUnit (f a) from by
      rintro ⟨a, n, rfl⟩
      simpa only [map_pow] using hunit.pow n)).mpr
  intro a b
  constructor
  · intro h
    have h' := congrArg (IsLocalization.Away.lift (θ N) hunit : T →+* D) h
    simpa only [IsLocalization.Away.lift_eq] using h'
  · intro h
    exact congrArg (algebraMap C T) (hf h)

def inverseLocalizationHom : S →+* T :=
  IsLocalization.Away.lift N
    (show IsUnit (((algebraMap C T).comp θ) N) from
      IsLocalization.Away.algebraMap_isUnit (θ N))

def forwardLocalizationHom : T →+* S :=
  IsLocalization.Away.lift (θ N) (by
    change IsUnit (φ (θ N))
    rw [← RingHom.comp_apply, hfirst]
    exact IsLocalization.Away.algebraMap_isUnit N)

theorem inverseLocalizationHom_base (p : P) :
    inverseLocalizationHom (T := T) N θ (algebraMap P S p) = algebraMap C T (θ p) :=
  IsLocalization.Away.lift_eq _ _ _

theorem forwardLocalizationHom_base (c : C) :
    forwardLocalizationHom (T := T) N θ φ hfirst (algebraMap C T c) = φ c :=
  IsLocalization.Away.lift_eq _ _ _

/-- The first actual identity on the entire plane localization follows
from the already derived polynomial inverse identities. -/
theorem forward_comp_inverseLocalizationHom :
    (forwardLocalizationHom (T := T) N θ φ hfirst).comp
      (inverseLocalizationHom (S := S) (T := T) N θ) = RingHom.id S := by
  apply IsLocalization.ringHom_ext (Submonoid.powers N)
  apply RingHom.ext
  intro p
  simp only [RingHom.comp_apply, inverseLocalizationHom_base,
    forwardLocalizationHom_base, RingHom.id_apply]
  exact RingHom.congr_fun hfirst p

/-- Once coordinate reconstruction has proved the whole-chart identity,
the universal property extends it to the entire original inverse domain. -/
theorem inverse_comp_forwardLocalizationHom
    (hchart : (inverseLocalizationHom (S := S) (T := T) N θ).comp φ = algebraMap C T) :
    (inverseLocalizationHom (S := S) (T := T) N θ).comp
      (forwardLocalizationHom (T := T) N θ φ hfirst) = RingHom.id T := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (θ N))
  apply RingHom.ext
  intro c
  simp only [RingHom.comp_apply, forwardLocalizationHom_base, RingHom.id_apply]
  exact RingHom.congr_fun hchart c

def chartLocalizationRingEquiv
    (hchart : (inverseLocalizationHom (S := S) (T := T) N θ).comp φ = algebraMap C T) :
    S ≃+* T where
  __ := inverseLocalizationHom (S := S) (T := T) N θ
  invFun := forwardLocalizationHom (T := T) N θ φ hfirst
  left_inv := fun s => RingHom.congr_fun
    (forward_comp_inverseLocalizationHom (T := T) N θ φ hfirst) s
  right_inv := fun t => RingHom.congr_fun
    (inverse_comp_forwardLocalizationHom (T := T) N θ φ hfirst hchart) t

end PfaffianDescent.QuadraticSkewRationality.SecondComposite005
