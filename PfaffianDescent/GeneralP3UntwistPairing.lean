import PfaffianDescent.ProjectiveMixedTwistPairing
import PfaffianDescent.P3TwistTensorEquivalence

/-! SOURCE ONLY / UNVERIFIED. Actual all-degree untwisting on P3.
This is the native multiplication O(m) tensor O(-(m+d)) -> O(-d),
not a supplied line-bundle identification or RR/duality certificate. -/
noncomputable section
namespace PfaffianDescent.ProjectiveNegativeTwist
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PolyA" => MvPolynomial (Fin 4) K
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

/-- The actual product, with the negative difference expressed by its
complementary degree 0+d, so the raw multiplication-to-zero square is
literal even for abstract d. The final weighted Iso identifies 0+d with d. -/
def p3UntwistPairingPresheaf (m d : ℕ) :
    PresheafOfModules.Monoidal.tensorObj (R := (Proj PS).sheaf.obj)
      (positiveModulePresheaf PS m) (modulePresheaf PS (m + d)) ⟶
      modulePresheaf PS (0 + d) where
  app U := ModuleCat.MonoidalCategory.tensorLift
    (fun p q =>
      ⟨fun x => p.1 x * q.1 x, by
        simpa only [Nat.add_sub_cancel_left, Nat.zero_add] using
          isLocallyPositiveSectionFraction_mul_locallySectionFraction_of_le
            PS m (m + d) (Nat.le_add_right m d) p.2 q.2⟩)
    (by
      intro p q r
      apply Subtype.ext
      funext x
      exact add_mul _ _ _)
    (by
      intro r p q
      apply Subtype.ext
      funext x
      change ((r.1 x).val * p.1 x) * q.1 x = (r.1 x).val * (p.1 x * q.1 x)
      ring)
    (by
      intro p q r
      apply Subtype.ext
      funext x
      exact mul_add _ _ _)
    (by
      intro r p q
      apply Subtype.ext
      funext x
      change p.1 x * ((r.1 x).val * q.1 x) = (r.1 x).val * (p.1 x * q.1 x)
      ring)
  naturality := by
    intro U V i
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro p q
    apply Subtype.ext
    funext x
    rfl

/-- Native sheaf multiplication for the actual complementary degrees. -/
def p3UntwistPairing (m d : ℕ) :
    schemeModuleTensor (positiveSheafOfModules PS m) (sheafOfModules PS (m + d)) ⟶
      sheafOfModules PS (0 + d) :=
  ((PresheafOfModules.sheafificationAdjunction
    (𝟙 (Proj PS).ringCatSheaf.obj)).homEquiv _ _).symm
      (p3UntwistPairingPresheaf K m d)

private theorem p3UntwistPairing_raw_square (m d : ℕ) (s : PS d) :
    PresheafOfModules.Monoidal.tensorHom (positiveMulHomogeneous PS s m).val
      (𝟙 (modulePresheaf PS (m + d))) ≫ positiveNegativePairingPresheaf PS (m + d) =
    p3UntwistPairingPresheaf K m d ≫ (mulHomogeneous PS s 0).val := by
  ext1 U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro p q
  apply Subtype.ext
  funext x
  change (algebraMap PolyA (PositiveFiber PS x.1) (s : PolyA) * p.1 x) * q.1 x =
    algebraMap PolyA (PositiveFiber PS x.1) (s : PolyA) * (p.1 x * q.1 x)
  ring

/-- Actual multiplication square used to prove local invertibility. -/
theorem p3UntwistPairing_square (m d : ℕ) (s : PS d) :
    schemeModuleTensorMap (positiveMulHomogeneous PS s m)
      (𝟙 (sheafOfModules PS (m + d))) ≫ positiveNegativePairing PS (m + d) =
    p3UntwistPairing K m d ≫ mulHomogeneous PS s 0 := by
  rw [schemeModuleTensorMap_eq_sheafification]
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (Proj PS).ringCatSheaf.obj)
  have hpair : adj.homEquiv _ _ (positiveNegativePairing PS (m + d)) =
      positiveNegativePairingPresheaf PS (m + d) :=
    (adj.homEquiv _ _).apply_symm_apply _
  have hdiff : adj.homEquiv _ _ (p3UntwistPairing K m d) =
      p3UntwistPairingPresheaf K m d := (adj.homEquiv _ _).apply_symm_apply _
  apply (adj.homEquiv _ _).injective
  erw [adj.homEquiv_naturality_left]
  rw [hpair]
  erw [adj.homEquiv_naturality_right]
  rw [hdiff]
  exact p3UntwistPairing_raw_square K m d s

/-- The zero-difference value is exactly the existing inverse pairing. -/
theorem p3UntwistPairing_zero (m : ℕ) :
    p3UntwistPairing K m 0 = positiveNegativePairing PS m := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (Proj PS).ringCatSheaf.obj)
  have hdiff : adj.homEquiv _ _ (p3UntwistPairing K m 0) =
      p3UntwistPairingPresheaf K m 0 := (adj.homEquiv _ _).apply_symm_apply _
  have hpair : adj.homEquiv _ _ (positiveNegativePairing PS m) =
      positiveNegativePairingPresheaf PS m := (adj.homEquiv _ _).apply_symm_apply _
  have hpraw : p3UntwistPairingPresheaf K m 0 =
      positiveNegativePairingPresheaf PS m := by
    ext1 U
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro p q
    apply Subtype.ext
    funext x
    rfl
  apply (adj.homEquiv _ _).injective
  exact hdiff.trans (hpraw.trans hpair.symm)

/-- Every actual coordinate chart makes the complementary-degree product
invertible; the d=0 case uses the accepted actual inverse pairing. -/
theorem p3CoordinateUntwistPairing_isIso (j : Fin 4) (m d : ℕ) :
    IsIso ((Scheme.Modules.restrictFunctor (p3StandardOpen (K := K) j).ι).map
      (p3UntwistPairing K m d)) := by
  by_cases hd : d = 0
  · subst d
    rw [p3UntwistPairing_zero]
    exact p3CoordinatePositiveNegativePairing_isIso K j m
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd
  let U := p3StandardOpen (K := K) j
  let F := Scheme.Modules.restrictFunctor U.ι
  let s := degreeOnePower PS (p3Coordinate K j) d
  have hspan : (HomogeneousIdeal.irrelevant PS).toIdeal ≤
      Ideal.span (Set.range (fun f : PS 1 => (f : PolyA))) :=
    (p3Coordinates_span_irrelevant K).trans (Ideal.span_mono (by
      rintro _ ⟨i, rfl⟩
      exact ⟨p3Coordinate K i, rfl⟩))
  have hU : homogeneousBasicOpen PS (s : PolyA) = U := by
    exact ProjectiveSpectrum.basicOpen_pow PS (MvPolynomial.X j) d hdpos
  letI : IsIso (F.map (positiveMulHomogeneous PS s m)) := by
    dsimp only [F]
    rw [← hU]
    exact restrict_positiveMulHomogeneous_isIso_on_basicOpen PS s m hspan
  letI : IsIso (F.map (mulHomogeneous PS s 0)) := by
    dsimp only [F]
    rw [← hU]
    exact restrict_mulHomogeneous_isIso_on_basicOpen PS s 0 hspan
  letI : IsIso (F.map (positiveNegativePairing PS (m + d))) :=
    p3CoordinatePositiveNegativePairing_isIso K j (m + d)
  letI : IsIso (F.map (schemeModuleTensorMap
      (positiveMulHomogeneous PS s m) (𝟙 (sheafOfModules PS (m + d))))) :=
    restrict_schemeModuleTensorMap_isIso_of_isIso U
      (positiveMulHomogeneous PS s m) (𝟙 (sheafOfModules PS (m + d)))
  have h := congrArg F.map (p3UntwistPairing_square K m d s)
  rw [F.map_comp, F.map_comp] at h
  haveI : IsIso (F.map (p3UntwistPairing K m d) ≫ F.map (mulHomogeneous PS s 0)) := by
    rw [← h]
    infer_instance
  exact IsIso.of_isIso_comp_right
    (F.map (p3UntwistPairing K m d)) (F.map (mulHomogeneous PS s 0))

/-- ALL complementary-degree untwist products are genuine native Isos. -/
theorem p3UntwistPairing_isIso (m d : ℕ) : IsIso (p3UntwistPairing K m d) := by
  let U := p3StandardOpenLifted (K := K)
  let F : ∀ j : P3CoordinateIndex, (Proj PS).Modules ⥤
      SheafOfModules ((Proj PS).ringCatSheaf.over (U j)) :=
    fun j => SheafOfModules.overFunctor (Proj PS).ringCatSheaf (U j)
  let hF : JointlyReflectIsomorphisms F :=
    SheafOfModules.overFunctors_jointlyReflectIsomorphisms U
      (p3StandardOpenLifted_coversTop K)
  letI : ∀ j, IsIso ((F j).map (p3UntwistPairing K m d)) := fun j => by
    letI : IsIso ((Scheme.Modules.restrictFunctor
        (p3StandardOpen (K := K) j.down).ι).map (p3UntwistPairing K m d)) :=
      p3CoordinateUntwistPairing_isIso K j.down m d
    exact overFunctorMap_isIso_of_restrictMap_isIso
      (p3StandardOpen (K := K) j.down) (p3UntwistPairing K m d)
  exact hF.isIso (p3UntwistPairing K m d)

/-- Untwist the actual weighted positive free summand back to O(-d). -/
def p3WeightedFreeTermUntwistIso (B d : ℕ) (hd : d ≤ B) :
    schemeModuleTensor (positiveSheafOfModules PS (B - d)) (sheafOfModules PS B) ≅
      sheafOfModules PS d := by
  have hB : B - d + d = B := Nat.sub_add_cancel hd
  letI : IsIso (p3UntwistPairing K (B - d) d) := p3UntwistPairing_isIso K (B - d) d
  exact (schemeModuleTensorMapIso (Iso.refl _)
    (eqToIso (congrArg (sheafOfModules PS) hB)).symm) ≪≫
      asIso (p3UntwistPairing K (B - d) d) ≪≫
        eqToIso (congrArg (sheafOfModules PS) (Nat.zero_add d))

end PfaffianDescent.ProjectiveNegativeTwist
