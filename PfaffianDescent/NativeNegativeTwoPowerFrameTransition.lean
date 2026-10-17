import PfaffianDescent.VoisinProjectiveSpaceCech
import AllCharacteristics.GradedChartCoordinates

/- SOURCE ONLY / UNVERIFIED. Native negative O(-2) frames and WHOLE section
transitions under original structure-sheaf scalar multiplication. -/
noncomputable section
namespace PfaffianDescent.ProjectiveNegativeTwist
open AlgebraicGeometry CategoryTheory Opposite HomogeneousLocalization
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {A ρ : Type u} [CommRing A] [SetLike ρ A] [AddSubgroupClass ρ A]
variable (G : ℕ → ρ) [GradedRing G]
local instance negativeTwo_pointIdeal_prime (x : Proj G) :
    (pointIdeal G x).IsPrime := ProjectiveSpectrum.isPrime x

/-- Actual q/ell² coefficient on ANY original subopen of D_+(ell). -/
def nativeNegativeTwoCoefficient (ell : G 1) (q : G 2)
    (U : (Proj G).Opens) (hU : U ≤ Proj.basicOpen G (ell : A)) : Γ(Proj G, U) :=
  (Proj G).presheaf.map (homOfLE hU).op
    ((Proj.awayToSection G (ell : A)).hom
      (Away.mk G ell.2 2 (q : A) (by simpa using q.2)))

/-- The literal negative power frame, the ORIGINAL multiplication-to-unit map. -/
def nativeNegativeTwoPowerFrameHom (ell : G 1) :
    sheafOfModules G 2 ⟶ SheafOfModules.unit (Proj G).ringCatSheaf :=
  mulHomogeneousToUnit G (degreeOnePower G ell 2)

/-- Generic original multiplier/unit cancellation. The older similarly named
provider is polynomial/Field-specific; this proof retains arbitrary actual grading. -/
theorem nativeNegativeTwo_mulToUnit_comp_unitToZeroTwist {d : ℕ} (q : G d) :
    mulHomogeneousToUnit G q ≫ unitToZeroTwist G = mulHomogeneous G q 0 := by
  change (mulHomogeneous G q 0 ≫ (unitIsoZeroTwist G).inv) ≫
    (unitIsoZeroTwist G).hom = _
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Actual localized fraction law, with no integral-domain/cancellation premise. -/
theorem nativeNegativeTwoCoefficient_value_mul_power
    (ell : G 1) (q : G 2) (U : (Proj G).Opens)
    (hU : U ≤ Proj.basicOpen G (ell : A)) (x : U) :
    algebraMap A (Fiber G x.1) ((ell : A) ^ 2) *
      ((nativeNegativeTwoCoefficient G ell q U hU).val x).val =
        algebraMap A (Fiber G x.1) (q : A) := by
  change algebraMap A (Localization.AtPrime (pointIdeal G x.1)) ((ell : A) ^ 2) *
    (((Proj.awayToSection G (ell : A)).hom
      (Away.mk G ell.2 2 (q : A) (by simpa using q.2))).val ⟨x.1, hU x.2⟩).val = _
  have ha := ProjectiveSpectrum.Proj.awayToSection_apply G (ell : A)
    (Away.mk G ell.2 2 (q : A) (by simpa using q.2)) ⟨x.1, hU x.2⟩
  erw [ha, Away.val_mk]
  rw [Localization.mk_eq_mk', IsLocalization.map_mk']
  simp only [RingHom.id_apply]
  have hell : (ell : A) ∈ (pointIdeal G x.1).primeCompl := by
    rw [Ideal.mem_primeCompl_iff]
    exact (ProjectiveSpectrum.mem_basicOpen G (ell : A) x.1).mp (hU x.2)
  exact IsLocalization.mk'_spec'
    (M := (pointIdeal G x.1).primeCompl) (Localization.AtPrime (pointIdeal G x.1))
    (q : A) ⟨(ell : A) ^ 2, Submonoid.pow_mem _ hell 2⟩

/-- WHOLE native map coefficient on every subopen, not merely a stalk or rank law. -/
theorem nativeNegativeTwo_mulToUnit_coefficient
    (ell : G 1) (q : G 2) (U : (Proj G).Opens)
    (hU : U ≤ Proj.basicOpen G (ell : A)) (z : Γ(sheafOfModules G 2, U)) :
    (mulHomogeneousToUnit G q).val.app (op U) z =
      @Mul.mul (Γ(Proj G, U)) (inferInstance : Mul (Γ(Proj G, U)))
        (nativeNegativeTwoCoefficient G ell q U hU)
        ((nativeNegativeTwoPowerFrameHom G ell).val.app (op U) z : Γ(Proj G, U)) := by
  let e := (((Scheme.Modules.toPresheaf (Proj G)).mapIso (unitIsoZeroTwist G)).app (op U))
  have hqz := congrArg
    (fun f : sheafOfModules G 2 ⟶ sheafOfModules G 0 => f.val.app (op U) z)
    (nativeNegativeTwo_mulToUnit_comp_unitToZeroTwist G q)
  have hcz := congrArg
    (fun f : sheafOfModules G 2 ⟶ sheafOfModules G 0 => f.val.app (op U) z)
    (nativeNegativeTwo_mulToUnit_comp_unitToZeroTwist G (degreeOnePower G ell 2))
  change (unitToZeroTwist G).val.app (op U)
    ((mulHomogeneousToUnit G q).val.app (op U) z) =
      (mulHomogeneous G q 0).val.app (op U) z at hqz
  change (unitToZeroTwist G).val.app (op U)
    ((nativeNegativeTwoPowerFrameHom G ell).val.app (op U) z) =
      (mulHomogeneous G (degreeOnePower G ell 2) 0).val.app (op U) z at hcz
  apply (ConcreteCategory.bijective_of_isIso e.hom).injective
  change (unitToZeroTwist G).val.app (op U)
    ((mulHomogeneousToUnit G q).val.app (op U) z) = _
  refine hqz.trans ?_
  apply Subtype.ext
  funext x
  have hczx := congrArg (fun w => w.val x) hcz
  change algebraMap A (Fiber G x.1) (q : A) * z.val x =
    ((nativeNegativeTwoCoefficient G ell q U hU).val x *
      ((nativeNegativeTwoPowerFrameHom G ell).val.app (op U) z).val x).val
  refine Eq.trans ?_ (HomogeneousLocalization.val_mul
    ((nativeNegativeTwoCoefficient G ell q U hU).val x)
    (((nativeNegativeTwoPowerFrameHom G ell).val.app (op U) z).val x)).symm
  change (((nativeNegativeTwoPowerFrameHom G ell).val.app (op U) z).val x).val =
    algebraMap A (Fiber G x.1) ((ell : A) ^ 2) * z.val x at hczx
  rw [hczx]
  calc
    _ = (algebraMap A (Fiber G x.1) ((ell : A) ^ 2) *
        ((nativeNegativeTwoCoefficient G ell q U hU).val x).val) * z.val x := by
      rw [nativeNegativeTwoCoefficient_value_mul_power]
    _ = _ := by ring

/-- The degree-one normalized coefficient, using the ORIGINAL Away fraction. -/
def nativeDegreeOneRatioOnSubopen (ell eta : G 1)
    (U : (Proj G).Opens) (hU : U ≤ Proj.basicOpen G (ell : A)) : Γ(Proj G, U) :=
  (Proj G).presheaf.map (homOfLE hU).op
    ((Proj.awayToSection G (ell : A)).hom
      (Away.mk G ell.2 1 (eta : A) (by simpa using eta.2)))

/-- A square ratio is exactly the native quadratic coefficient as ENTIRE sections. -/
theorem nativeNegativeTwoCoefficient_squareRatio
    (ell eta : G 1) (U : (Proj G).Opens) (hU : U ≤ Proj.basicOpen G (ell : A)) :
    nativeNegativeTwoCoefficient G ell (degreeOnePower G eta 2) U hU =
      nativeDegreeOneRatioOnSubopen G ell eta U hU ^ 2 := by
  have hmk : Away.mk G ell.2 2 ((eta : A) ^ 2)
      (by exact (degreeOnePower G eta 2).2) =
      (Away.mk G ell.2 1 (eta : A) (by simpa using eta.2)) ^ 2 := by
    apply HomogeneousLocalization.val_injective
    simp only [Away.val_mk, HomogeneousLocalization.val_pow, Localization.mk_pow, pow_one]
    rfl
  unfold nativeNegativeTwoCoefficient nativeDegreeOneRatioOnSubopen
  change (Proj G).presheaf.map (homOfLE hU).op
    ((Proj.awayToSection G (ell : A)).hom
      (Away.mk G ell.2 2 ((eta : A) ^ 2) _)) = _
  rw [hmk, map_pow, map_pow]

/-- WHOLE O(-2) transition on EVERY subopen where ell is nonzero. -/
theorem nativeNegativeTwoPowerFrameHom_transition
    (ell eta : G 1) (U : (Proj G).Opens)
    (hU : U ≤ Proj.basicOpen G (ell : A)) (z : Γ(sheafOfModules G 2, U)) :
    (nativeNegativeTwoPowerFrameHom G eta).val.app (op U) z =
      @Mul.mul (Γ(Proj G, U)) (inferInstance : Mul (Γ(Proj G, U)))
        (nativeDegreeOneRatioOnSubopen G ell eta U hU ^ 2)
        ((nativeNegativeTwoPowerFrameHom G ell).val.app (op U) z : Γ(Proj G, U)) := by
  have h := nativeNegativeTwo_mulToUnit_coefficient G ell (degreeOnePower G eta 2) U hU z
  rw [nativeNegativeTwoCoefficient_squareRatio] at h
  exact h

/-- The native power frame is internally invertible on its ORIGINAL coordinate open. -/
theorem nativeNegativeTwoPowerFrameHom_restrict_isIso
    (ell : G 1)
    (hspan : (HomogeneousIdeal.irrelevant G).toIdeal ≤
      Ideal.span (Set.range (fun f : G 1 => (f : A)))) :
    IsIso ((Scheme.Modules.restrictFunctor (Proj.basicOpen G (ell : A)).ι).map
      (nativeNegativeTwoPowerFrameHom G ell)) := by
  let U := Proj.basicOpen G (ell : A)
  let F := Scheme.Modules.restrictFunctor U.ι
  have hmul : IsIso (F.map (mulHomogeneous G (degreeOnePower G ell 2) 0)) := by
    apply restrict_map_isIso_of_stalk U
    intro x
    have hell : (ell : A) ∈ (pointIdeal G (U.ι x)).primeCompl := by
      rw [Ideal.mem_primeCompl_iff]
      exact (ProjectiveSpectrum.mem_basicOpen G (ell : A) (U.ι x)).mp x.2
    have hpow : ((degreeOnePower G ell 2 : G 2) : A) ∈
        (pointIdeal G (U.ι x)).primeCompl := Submonoid.pow_mem _ hell 2
    change IsIso ((TopCat.Presheaf.stalkFunctor _ (U.ι x)).map
      (mulHomogeneousPresheaf G (degreeOnePower G ell 2) 0))
    exact mulHomogeneous_stalkMap_isIso_of_mem_primeCompl_of_irrelevant_le_span
      G (degreeOnePower G ell 2) 0 (U.ι x) hpow hspan
  letI := hmul
  unfold nativeNegativeTwoPowerFrameHom mulHomogeneousToUnit
  rw [Functor.map_comp]
  infer_instance

/-- Genuine native negative twist frame on the ORIGINAL basic-open scheme. -/
def nativeNegativeTwoPowerFrameRestrictionUnitIso
    (ell : G 1)
    (hspan : (HomogeneousIdeal.irrelevant G).toIdeal ≤
      Ideal.span (Set.range (fun f : G 1 => (f : A)))) :
    (Scheme.Modules.restrictFunctor (Proj.basicOpen G (ell : A)).ι).obj
        (sheafOfModules G 2) ≅
      SheafOfModules.unit (Proj.basicOpen G (ell : A) : Scheme).ringCatSheaf := by
  letI := nativeNegativeTwoPowerFrameHom_restrict_isIso G ell hspan
  exact asIso ((Scheme.Modules.restrictFunctor (Proj.basicOpen G (ell : A)).ι).map
      (nativeNegativeTwoPowerFrameHom G ell)) ≪≫
    Scheme.Modules.restrictUnitIso (Proj.basicOpen G (ell : A)).ι

end PfaffianDescent.ProjectiveNegativeTwist
end
