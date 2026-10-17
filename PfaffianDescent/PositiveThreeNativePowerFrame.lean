import AllCharacteristics.HomogeneousProjective
import PfaffianDescent.VoisinPositiveTwistTriviality
import PfaffianDescent.CubicClosedPointSerreTensorStalkUnitIso

/-! SOURCE ONLY. Literal native O(3) power frame and its actual section
values. This prepares whole overlap compatibility; no bundle-degree or global
pullback Iso is presumed. All scalars are original structure-sheaf scalars. -/
noncomputable section
namespace PfaffianDescent.ProjectiveNegativeTwist
open AlgebraicGeometry CategoryTheory HomogeneousLocalization Opposite
open AllCharacteristics.HomogeneousProjective BundleSectionZeroLocus
universe u
variable {A ρ : Type u} [CommRing A] [SetLike ρ A] [AddSubgroupClass ρ A]
variable (G : ℕ → ρ) [GradedRing G]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private instance nativePositivePointIdealPrime (x : Proj G) :
    (positivePointIdeal G x).IsPrime := ProjectiveSpectrum.isPrime x

private lemma nativeDegreeOnePower_coe (f : G 1) (m : ℕ) :
    ((degreeOnePower G f m : G m) : A) = (f : A) ^ m := rfl
attribute [local simp] nativeDegreeOnePower_coe

/-- Restriction of the actual homogeneous section retains its literal
fraction at EVERY point, derived from the original whole-family law. -/
private lemma nativePositiveGlobalHomogeneousFamily_value
    (m : ℕ) (q : G m) (U : (Proj G).Opens) (x : U) :
    ((positiveGlobalSectionOfHomogeneous G m q).val (op U)).1 x =
      Localization.mk (q : A) ⟨1, Submonoid.one_mem _⟩ := by
  let M := positiveSheafOfModules G m
  let s := positiveGlobalSectionOfHomogeneous G m q
  have hs : M.presheaf.map
      (homOfLE (show U ≤ (⊤ : (Proj G).Opens) from le_top)).op
      (s.val (op ⊤)) = s.val (op U) :=
    s.property (homOfLE (show U ≤ (⊤ : (Proj G).Opens) from le_top)).op
  have hx := congrArg (fun z : Γ(M, U) => z.1 x) hs
  change (s.val (op ⊤)).1 ⟨x.1, trivial⟩ = (s.val (op U)).1 x at hx
  have hv := positiveSectionValue_positiveGlobalSectionOfHomogeneous G m q x.1
  change (s.val (op ⊤)).1 ⟨x.1, trivial⟩ =
    Localization.mk (q : A) ⟨1, Submonoid.one_mem _⟩ at hv
  exact hx.symm.trans hv

/-- Three actual native degree-one multiplications equal actual multiplication
by the third power, as ENTIRE module-sheaf morphisms. -/
theorem positiveMulHomogeneous_three_degreeOne_comp
    (ell : G 1) :
    positiveMulHomogeneous G ell 0 ≫ positiveMulHomogeneous G ell 1 ≫
        positiveMulHomogeneous G ell 2 =
      positiveMulHomogeneous G (degreeOnePower G ell 3) 0 := by
  ext U z
  apply Subtype.ext
  funext x
  change algebraMap A (PositiveFiber G x.1) (ell : A) *
      (algebraMap A (PositiveFiber G x.1) (ell : A) *
        (algebraMap A (PositiveFiber G x.1) (ell : A) * z.1 x)) =
    algebraMap A (PositiveFiber G x.1) ((ell : A) ^ 3) * z.1 x
  rw [map_pow]
  ring

/-- The actual native cubic-power frame, with literal natural-number indices
so no arbitrary degree-equality transport enters this map. -/
def positiveThreePowerFrameHom (ell : G 1) :
    SheafOfModules.unit (Proj G).ringCatSheaf ⟶ positiveSheafOfModules G 3 :=
  unitToZeroTwist G ≫ zeroTwistToPositiveZero G ≫
    positiveMulHomogeneous G (degreeOnePower G ell 3) 0

/-- The canonical power frame is the same entire map as the three original
native degree-one multiplications. -/
theorem positiveThreePowerFrameHom_eq_iterated (ell : G 1) :
    positiveThreePowerFrameHom G ell =
      unitToZeroTwist G ≫ zeroTwistToPositiveZero G ≫
        positiveMulHomogeneous G ell 0 ≫ positiveMulHomogeneous G ell 1 ≫
          positiveMulHomogeneous G ell 2 := by
  unfold positiveThreePowerFrameHom
  rw [← positiveMulHomogeneous_three_degreeOne_comp]

/-- The actual section value of the cubic-power frame is its literal cubic
multiplier times the ORIGINAL structure-sheaf section value. -/
theorem positiveThreePowerFrameHom_apply_value
    (ell : G 1) (U : (Proj G).Opens) (r : Γ(Proj G, U)) (x : U) :
    ((positiveThreePowerFrameHom G ell).val.app (op U) r).1 x =
      algebraMap A (PositiveFiber G x.1) ((ell : A) ^ 3) * (r.val x).val := by
  rfl

/-- Native power-frame invertibility is internally proved at every original
stalk on D_+(ell), not supplied as a local triviality certificate. -/
theorem positiveThreePowerFrameHom_restrict_isIso
    (ell : G 1)
    (hspan : (HomogeneousIdeal.irrelevant G).toIdeal ≤
      Ideal.span (Set.range (fun f : G 1 => (f : A)))) :
    IsIso ((Scheme.Modules.restrictFunctor
      (Proj.basicOpen G (ell : A)).ι).map (positiveThreePowerFrameHom G ell)) := by
  let U := Proj.basicOpen G (ell : A)
  let F := Scheme.Modules.restrictFunctor U.ι
  have hmul : IsIso (F.map
      (positiveMulHomogeneous G (degreeOnePower G ell 3) 0)) := by
    apply restrict_map_isIso_of_stalk U
    intro x
    letI : (positivePointIdeal G (U.ι x)).IsPrime := ProjectiveSpectrum.isPrime (U.ι x)
    have hell : (ell : A) ∈ (positivePointIdeal G (U.ι x)).primeCompl := by
      rw [Ideal.mem_primeCompl_iff]
      exact (ProjectiveSpectrum.mem_basicOpen G (ell : A) (U.ι x)).mp x.2
    have hpow : ((degreeOnePower G ell 3 : G 3) : A) ∈
        (positivePointIdeal G (U.ι x)).primeCompl :=
      Submonoid.pow_mem _ hell 3
    change IsIso ((TopCat.Presheaf.stalkFunctor _ (U.ι x)).map
      (positiveMulHomogeneousPresheaf G (degreeOnePower G ell 3) 0))
    exact positiveMulHomogeneous_stalkMap_isIso_of_mem_primeCompl_of_irrelevant_le_span
      G (degreeOnePower G ell 3) 0 (U.ι x) hpow hspan
  letI : IsIso (F.map (unitToZeroTwist G)) := by
    change IsIso (F.map (unitIsoZeroTwist G).hom)
    exact Functor.map_isIso F (unitIsoZeroTwist G).hom
  letI : IsIso (F.map (zeroTwistToPositiveZero G)) := by
    change IsIso (F.map (positiveZeroTwistIso G).inv)
    infer_instance
  letI := hmul
  unfold positiveThreePowerFrameHom
  rw [Functor.map_comp, Functor.map_comp]
  infer_instance

/-- Genuine local power-frame Iso on the actual original basic open. -/
def positiveThreePowerFrameRestrictionUnitIso
    (ell : G 1)
    (hspan : (HomogeneousIdeal.irrelevant G).toIdeal ≤
      Ideal.span (Set.range (fun f : G 1 => (f : A)))) :
    (Scheme.Modules.restrictFunctor (Proj.basicOpen G (ell : A)).ι).obj
      (positiveSheafOfModules G 3) ≅
      SheafOfModules.unit (Proj.basicOpen G (ell : A) : Scheme).ringCatSheaf := by
  letI := positiveThreePowerFrameHom_restrict_isIso G ell hspan
  exact (asIso ((Scheme.Modules.restrictFunctor (Proj.basicOpen G (ell : A)).ι).map
    (positiveThreePowerFrameHom G ell))).symm ≪≫
      Scheme.Modules.restrictUnitIso (Proj.basicOpen G (ell : A)).ι

/-- The actual positive fraction coefficient cancels the literal cubic power
of the chosen frame at every ORIGINAL point of its whole chart. -/
theorem positiveThreePowerFrameHom_awayCoefficient_value
    (ell : G 1) (q : G 3) (x : Proj.basicOpen G (ell : A)) :
    algebraMap A (PositiveFiber G x.1) ((ell : A) ^ 3) *
      (((Proj.awayToSection G (ell : A)).hom
        (Away.mk G ell.2 3 (q : A) (by simpa using q.2))).val x).val =
      Localization.mk (q : A) ⟨1, Submonoid.one_mem _⟩ := by
  letI : (positivePointIdeal G x.1).IsPrime := ProjectiveSpectrum.isPrime x.1
  have hell : (ell : A) ∈ (positivePointIdeal G x.1).primeCompl := by
    rw [Ideal.mem_primeCompl_iff]
    exact (ProjectiveSpectrum.mem_basicOpen G (ell : A) x.1).mp x.2
  have h := ProjectiveSpectrum.Proj.awayToSection_apply G (ell : A)
    (Away.mk G ell.2 3 (q : A) (by simpa using q.2)) x
  erw [h, Away.val_mk]
  rw [Localization.mk_eq_mk', IsLocalization.map_mk']
  simp only [RingHom.id_apply]
  erw [Localization.mk_one_eq_algebraMap]
  exact IsLocalization.mk'_spec'
    (M := (positivePointIdeal G x.1).primeCompl)
    (Localization.AtPrime (positivePointIdeal G x.1))
    (q : A) ⟨(ell : A) ^ 3, Submonoid.pow_mem _ hell 3⟩

/-- WHOLE native frame action on the literal fraction coefficient, equaling
the actual restricted homogeneous O(3) section, not merely its stalk rank. -/
theorem positiveThreePowerFrameHom_awayCoefficient_section
    (ell : G 1) (q : G 3) :
    (positiveThreePowerFrameHom G ell).val.app
      (op (Proj.basicOpen G (ell : A)))
      ((Proj.awayToSection G (ell : A)).hom
        (Away.mk G ell.2 3 (q : A) (by simpa using q.2))) =
      (positiveGlobalSectionOfHomogeneous G 3 q).val
        (op (Proj.basicOpen G (ell : A))) := by
  apply Subtype.ext
  funext x
  rw [positiveThreePowerFrameHom_apply_value]
  exact positiveThreePowerFrameHom_awayCoefficient_value G ell q x

/-- On EVERY actual open, the original frame applied to the actual unit
section is the actual homogeneous cubic-power section. -/
theorem positiveThreePowerFrameHom_one_eq_homogeneousSection
    (ell : G 1) (U : (Proj G).Opens) :
    (positiveThreePowerFrameHom G ell).val.app (op U) (1 : Γ(Proj G, U)) =
      (positiveGlobalSectionOfHomogeneous G 3 (degreeOnePower G ell 3)).val (op U) := by
  apply Subtype.ext
  funext x
  rw [positiveThreePowerFrameHom_apply_value,
    nativePositiveGlobalHomogeneousFamily_value]
  have hone : ((1 : Γ(Proj G, U)).val x).val = (1 : PositiveFiber G x.1) := by
    simp only [AlgebraicGeometry.Proj.one_apply, HomogeneousLocalization.val_one]
  rw [hone]
  change algebraMap A (PositiveFiber G x.1) ((ell : A) ^ 3) * 1 =
    Localization.mk ((ell : A) ^ 3) ⟨1, Submonoid.one_mem _⟩
  rw [mul_one]
  exact (Localization.mk_one_eq_algebraMap
    (M := (positivePointIdeal G x.1).primeCompl) ((ell : A) ^ 3)).symm

/-- WHOLE chart frame transition: the other actual O(3) frame is the original
frame multiplied by the actual ratio eta^3/ell^3. This equality involves native
module sheaf sections, including all points of the original open. -/
theorem positiveThreePowerFrameHom_native_transition_section
    (ell eta : G 1) :
    (positiveThreePowerFrameHom G ell).val.app
      (op (Proj.basicOpen G (ell : A)))
      ((Proj.awayToSection G (ell : A)).hom
        (Away.mk G ell.2 3 ((eta : A) ^ 3) (by
          simpa using (degreeOnePower G eta 3).2))) =
      (positiveThreePowerFrameHom G eta).val.app
        (op (Proj.basicOpen G (ell : A))) (1 : Γ(Proj G, Proj.basicOpen G (ell : A))) := by
  rw [positiveThreePowerFrameHom_one_eq_homogeneousSection]
  exact positiveThreePowerFrameHom_awayCoefficient_section G ell (degreeOnePower G eta 3)

end PfaffianDescent.ProjectiveNegativeTwist
