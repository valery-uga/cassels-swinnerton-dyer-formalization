import PfaffianDescent.VoisinTwistCechTerms

/-!
# Naturality of the Laurent model for negative-twist Cech terms

This file proves that the Laurent representative of a section of `O(-m)` is
independent of the coordinate used to trivialize the twist.  The proof
evaluates at the generic point of projective three-space, where localization
is injective, and compares the two coordinate trivializations there.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry MvPolynomial Opposite
open scoped AddMonoidAlgebra BigOperators
universe u
namespace PfaffianDescent.TwistCechTerms

open LaurentLocalization TwistLaurent
open ProjectiveNegativeTwist

variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "S" => MvPolynomial (Fin 4) K
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

/-- The generic point of projective space, represented by the zero homogeneous ideal. -/
def p3GenericPoint : ProjectiveSpectrum PS where
  asHomogeneousIdeal := ⊥
  isPrime := by
    rw [HomogeneousIdeal.toIdeal_bot]
    exact Ideal.isPrime_bot
  not_irrelevant_le := by
    intro h
    have hx : (MvPolynomial.X (0 : Fin 4) : S) ∈ (⊥ : HomogeneousIdeal PS) :=
      h (HomogeneousIdeal.mem_irrelevant_of_mem PS (by decide : 0 < 1)
        (MvPolynomial.isHomogeneous_X K 0))
    change (MvPolynomial.X (0 : Fin 4) : S) ∈ (⊥ : Ideal S) at hx
    exact MvPolynomial.X_ne_zero 0 (Ideal.mem_bot.mp hx)

@[simp] lemma p3GenericPoint_asHomogeneousIdeal :
    (p3GenericPoint K).asHomogeneousIdeal = ⊥ := rfl

@[simp] lemma p3GenericPoint_pointIdeal :
    pointIdeal PS (p3GenericPoint K) = ⊥ := by
  simp [pointIdeal, p3GenericPoint]

lemma p3GenericPoint_mem_basicOpen_cechDenominator
    (n : ℕ) (f : Fin (n + 1) → Fin 4) :
    p3GenericPoint K ∈ AlgebraicGeometry.Proj.basicOpen PS
      (p3CechDenominator (K := K) n f) := by
  change p3CechDenominator (K := K) n f ∉
    (p3GenericPoint K).asHomogeneousIdeal
  change p3CechDenominator (K := K) n f ∉ (⊥ : Ideal S)
  rw [Ideal.mem_bot]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => MvPolynomial.X_ne_zero (f i))

set_option backward.isDefEq.respectTransparency false in
def coordinateMultiplyToZero (i : Fin 4) (m : ℕ) :
    sheafOfModules PS m ⟶ sheafOfModules PS 0 where
  val :=
    { app := fun U ↦ by
        letI : Module ((Proj PS).ringCatSheaf.obj.obj U)
            ((presheafInAddCommGrp PS m).obj U) := by
          change Module ((ProjectiveSpectrum.Proj.structureSheaf PS).1.obj U)
            ((sheafInType PS m).1.obj U)
          infer_instance
        letI : Module ((Proj PS).ringCatSheaf.obj.obj U)
            ((presheafInAddCommGrp PS 0).obj U) := by
          change Module ((ProjectiveSpectrum.Proj.structureSheaf PS).1.obj U)
            ((sheafInType PS 0).1.obj U)
          infer_instance
        exact ModuleCat.ofHom
          { toFun := fun f ↦
              ⟨fun x ↦ algebraMap S (Fiber PS x.1)
                  ((degreeOnePower PS (p3Coordinate K i) m : PS m) : S) * f.1 x,
                isLocallySectionFraction_mulHomogeneous PS
                  (degreeOnePower PS (p3Coordinate K i) m) 0
                  (by simpa only [Nat.zero_add] using f.2)⟩
            map_add' := fun f g ↦ by
              apply Subtype.ext
              funext x
              exact mul_add _ _ _
            map_smul' := fun r f ↦ by
              apply Subtype.ext
              funext x
              change _ * ((r.1 x).val * f.1 x) =
                (r.1 x).val * (_ * f.1 x)
              ring }
      naturality := by
        intro U V h
        ext f
        rfl }

lemma coordinateMultiplyToZero_apply_val
    (i : Fin 4) (m : ℕ) (U : Scheme.Opens (Proj PS))
    (s : Γ(sheafOfModules PS m, U)) (x : U) :
    ((coordinateMultiplyToZero K i m).val.app (op U) s).1 x =
      algebraMap S (Fiber PS x.1)
        ((degreeOnePower PS (p3Coordinate K i) m : PS m) : S) * s.1 x := by
  rfl

theorem zeroAddTwistEq (m : ℕ) :
    sheafOfModules PS m = sheafOfModules PS (0 + m) :=
  congrArg (sheafOfModules PS) (Nat.zero_add m).symm

lemma eqToHom_zeroAddTwist_apply_heq
    (m : ℕ) (U : (Scheme.Opens (Proj PS))ᵒᵖ)
    (z : (sheafOfModules PS m).val.obj U) :
    (((Scheme.Modules.toPresheaf (Proj PS)).map
      (eqToHom (zeroAddTwistEq K m))).app U z) ≍ z := by
  have hmor :
      (eqToHom (zeroAddTwistEq K m) :
        sheafOfModules PS m ⟶ sheafOfModules PS (0 + m)) ≍
        𝟙 (sheafOfModules PS m) :=
    eqToHom_heq_id_dom _ _ _
  have happ :
      ((Scheme.Modules.toPresheaf (Proj PS)).map
        (eqToHom (zeroAddTwistEq K m))).app U ≍
      ((Scheme.Modules.toPresheaf (Proj PS)).map
        (𝟙 (sheafOfModules PS m))).app U := by
    congr <;> exact Nat.zero_add m
  have hout :
      (((Scheme.Modules.toPresheaf (Proj PS)).map
        (eqToHom (zeroAddTwistEq K m))).app U) z ≍
      (((Scheme.Modules.toPresheaf (Proj PS)).map
        (𝟙 (sheafOfModules PS m))).app U) z := by
    congr <;> simp only [Nat.zero_add]
  have hid :
      (((Scheme.Modules.toPresheaf (Proj PS)).map
        (𝟙 (sheafOfModules PS m))).app U) z = z := by rfl
  exact hout.trans (heq_of_eq hid)

lemma eqToHom_zeroAddTwist_apply_val
    (m : ℕ) (U : (Scheme.Opens (Proj PS))ᵒᵖ)
    (z : (sheafOfModules PS m).val.obj U) (x : U.unop) :
    ((((eqToHom (zeroAddTwistEq K m) :
      sheafOfModules PS m ⟶ sheafOfModules PS (0 + m)).val.app U) z).1 x) =
      z.1 x := by
  have h := eqToHom_zeroAddTwist_apply_heq K m U z
  have hcoe :
      (((((Scheme.Modules.toPresheaf (Proj PS)).map
        (eqToHom (zeroAddTwistEq K m))).app U) z).1) = z.1 :=
    (Subtype.heq_iff_coe_eq (fun q => by simp only [Nat.zero_add])).mp h
  change (((((Scheme.Modules.toPresheaf (Proj PS)).map
    (eqToHom (zeroAddTwistEq K m))).app U) z).1 x) = z.1 x
  exact congrFun hcoe x

set_option backward.isDefEq.respectTransparency false in
lemma negativeTwistTrivializationHom_comp_unitToZeroTwist
    (i : Fin 4) (m : ℕ) :
    negativeTwistTrivializationHom K i m ≫ unitToZeroTwist PS =
      coordinateMultiplyToZero K i m := by
  dsimp only [negativeTwistTrivializationHom]
  change (_ ≫ (unitIsoZeroTwist PS).inv) ≫
      (unitIsoZeroTwist PS).hom = _
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  let p := zeroAddTwistEq K m
  have hcast :
      cast (congrArg (fun W : (Proj PS).Modules =>
        W ⟶ sheafOfModules PS 0) p.symm)
          (mulHomogeneous PS (degreeOnePower PS (p3Coordinate K i) m) 0) =
        eqToHom p ≫
          mulHomogeneous PS (degreeOnePower PS (p3Coordinate K i) m) 0 :=
    congrArg_cast_hom_left p _
  ext U z
  apply Subtype.ext
  funext x
  change (((cast (congrArg (fun W : (Proj PS).Modules =>
      W ⟶ sheafOfModules PS 0) p.symm)
        (mulHomogeneous PS (degreeOnePower PS (p3Coordinate K i) m) 0)).val.app U) z).1 x = _
  rw [hcast]
  change
    (((mulHomogeneous PS (degreeOnePower PS (p3Coordinate K i) m) 0).val.app U)
      (((eqToHom p : sheafOfModules PS m ⟶ sheafOfModules PS (0 + m)).val.app U) z)).1 x = _
  change _ *
      ((((eqToHom p : sheafOfModules PS m ⟶ sheafOfModules PS (0 + m)).val.app U) z).1 x) = _
  rw [eqToHom_zeroAddTwist_apply_val]
  rfl

lemma negativeTwistTrivializationHom_apply_val
    (i : Fin 4) (m : ℕ) (U : Scheme.Opens (Proj PS))
    (s : Γ(sheafOfModules PS m, U)) (x : U) :
    ((((Scheme.Modules.toPresheaf (Proj PS)).map
      (negativeTwistTrivializationHom K i m)).app (op U) s).1 x).val =
      algebraMap S (Fiber PS x.1)
        ((degreeOnePower PS (p3Coordinate K i) m : PS m) : S) * s.1 x := by
  have happ := congrArg
    (fun q : sheafOfModules PS m ⟶ sheafOfModules PS 0 =>
      ((Scheme.Modules.toPresheaf (Proj PS)).map q).app (op U) s)
    (negativeTwistTrivializationHom_comp_unitToZeroTwist K i m)
  have hval := congrArg (fun z => z.1 x) happ
  change
    ((((unitToZeroTwist PS).val.app (op U))
      (((negativeTwistTrivializationHom K i m).val.app (op U)) s)).1 x) =
      (((coordinateMultiplyToZero K i m).val.app (op U)) s).1 x at hval
  rw [coordinateMultiplyToZero_apply_val] at hval
  exact hval

namespace GenericEvaluation

variable (n : ℕ) (f : Fin (n + 1) → Fin 4)
local notation "D" => p3CechDenominator (K := K) n f

lemma cechDenominator_ne_zero : D ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => MvPolynomial.X_ne_zero (f i))

lemma cechDenominator_mem_genericPrimeCompl :
    D ∈ (⊥ : Ideal S).primeCompl := by
  rw [Ideal.mem_primeCompl_iff, Ideal.mem_bot]
  exact cechDenominator_ne_zero K n f

lemma genericPowersLE :
    Submonoid.powers D ≤
      Submonoid.comap (RingHom.id S) (⊥ : Ideal S).primeCompl := by
  intro x hx
  change x ∈ (⊥ : Ideal S).primeCompl
  exact (Submonoid.powers_le.mpr
    (cechDenominator_mem_genericPrimeCompl K n f)) hx

def genericLocalizationMap :
    Localization.Away D →+* Localization (⊥ : Ideal S).primeCompl :=
  IsLocalization.map (Localization (⊥ : Ideal S).primeCompl) (RingHom.id S)
    (genericPowersLE K n f)

lemma genericLocalizationMap_injective :
    Function.Injective (genericLocalizationMap K n f) := by
  exact IsLocalization.map_injective_of_injective'
    (Submonoid.powers D) S
    (Localization (⊥ : Ideal S).primeCompl)
    (f := RingHom.id S)
    (Rₘ := Localization.Away D)
    (N := (⊥ : Ideal S).primeCompl)
    (genericPowersLE K n f)
    (by
      intro h
      exact h (Ideal.zero_mem (⊥ : Ideal S)))
    (fun _ _ h => h)

lemma genericLocalizationMap_algebraMap (x : S) :
    genericLocalizationMap K n f
      (algebraMap S (Localization.Away D) x) =
      algebraMap S (Fiber PS (p3GenericPoint K)) x := by
  exact IsLocalization.map_eq (genericPowersLE K n f) x

lemma awayToSection_generic_apply
    (z : HomogeneousLocalization.Away PS D) :
    (((ProjectiveSpectrum.Proj.awayToSection PS D).1 z).val
      ⟨p3GenericPoint K,
        p3GenericPoint_mem_basicOpen_cechDenominator K n f⟩).val =
      genericLocalizationMap K n f z.val := by
  dsimp only [p3GenericPoint]
  unfold genericLocalizationMap
  rw [AlgebraicGeometry.ProjectiveSpectrum.Proj.awayToSection_apply]
  change (IsLocalization.map (Localization (⊥ : Ideal S).primeCompl)
      (RingHom.id S) _ z.val) =
    (IsLocalization.map (Localization (⊥ : Ideal S).primeCompl)
      (RingHom.id S) _ z.val)
  rfl


local notation "F" => forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat

abbrev cechBasicOpen : Scheme.Opens (Proj PS) :=
  AlgebraicGeometry.Proj.basicOpen PS D

abbrev cechGenericPoint : cechBasicOpen K n f :=
  ⟨p3GenericPoint K,
    p3GenericPoint_mem_basicOpen_cechDenominator K n f⟩

abbrev chartAway
    (m : ℕ) (i : Fin 4)
    (hdiv : MvPolynomial.X (R := K) i ∣ D)
    (s : Γ(sheafOfModules PS m, cechBasicOpen K n f)) :
    HomogeneousLocalization.Away PS D :=
  (p3NegativeTwistBasicOpenIsoAway K D (n + 1)
    (p3CechDenominator_mem (K := K) n f) (Nat.succ_pos n)
    i hdiv m).hom s

lemma awayToSection_chartAway
    (m : ℕ) (i : Fin 4)
    (hdiv : MvPolynomial.X (R := K) i ∣ D)
    (s : Γ(sheafOfModules PS m, cechBasicOpen K n f)) :
    (ProjectiveSpectrum.Proj.awayToSection PS D).hom (chartAway K n f m i hdiv s) =
      (negativeTwistSectionsIsoStructure K (cechBasicOpen K n f) i
        (AlgebraicGeometry.Proj.basicOpen_mono PS (MvPolynomial.X i) D hdiv) m).hom s := by
  let e := AlgebraicGeometry.Proj.basicOpenIsoAway PS D
    (p3CechDenominator_mem (K := K) n f) (Nat.succ_pos n)
  change e.hom
      ((p3NegativeTwistBasicOpenIsoAway K D (n + 1)
        (p3CechDenominator_mem (K := K) n f) (Nat.succ_pos n)
        i hdiv m).hom s) = _
  rw [p3NegativeTwistBasicOpenIsoAway_hom]
  change e.hom (e.inv
    ((negativeTwistSectionsIsoStructure K (cechBasicOpen K n f) i
      (AlgebraicGeometry.Proj.basicOpen_mono PS (MvPolynomial.X i) D hdiv) m).hom s)) = _
  exact e.inv_hom_id_apply _

lemma chartStructure_eq_trivialization
    (m : ℕ) (i : Fin 4)
    (hdiv : MvPolynomial.X (R := K) i ∣ D)
    (s : Γ(sheafOfModules PS m, cechBasicOpen K n f)) :
    (negativeTwistSectionsIsoStructure K (cechBasicOpen K n f) i
      (AlgebraicGeometry.Proj.basicOpen_mono PS (MvPolynomial.X i) D hdiv) m).hom s =
      ((Scheme.Modules.toPresheaf (Proj PS)).map
        (negativeTwistTrivializationHom K i m)).app
          (op (cechBasicOpen K n f)) s := by
  exact congrArg
    (fun q : Γ(sheafOfModules PS m, cechBasicOpen K n f) ⟶
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).obj
        Γ(Proj PS, cechBasicOpen K n f) => q s)
    (p3NegativeTwistSectionsIsoUnit_hom_topIso K
      (cechBasicOpen K n f) i
      (AlgebraicGeometry.Proj.basicOpen_mono PS (MvPolynomial.X i) D hdiv) m)

lemma genericLocalizationMap_chartAway
    (m : ℕ) (i : Fin 4)
    (hdiv : MvPolynomial.X (R := K) i ∣ D)
    (s : Γ(sheafOfModules PS m, cechBasicOpen K n f)) :
    genericLocalizationMap K n f (chartAway K n f m i hdiv s).val =
      algebraMap S (Fiber PS (p3GenericPoint K))
        ((degreeOnePower PS (p3Coordinate K i) m : PS m) : S) *
          s.1 (cechGenericPoint K n f) := by
  rw [← awayToSection_generic_apply K n f]
  have haway := awayToSection_chartAway K n f m i hdiv s
  have hchart := chartStructure_eq_trivialization K n f m i hdiv s
  calc
    _ = (((negativeTwistSectionsIsoStructure K (cechBasicOpen K n f) i
          (AlgebraicGeometry.Proj.basicOpen_mono PS (MvPolynomial.X i) D hdiv) m).hom s).1
        (cechGenericPoint K n f)).val :=
      congrArg (fun r => (r.1 (cechGenericPoint K n f)).val) haway
    _ = (((((Scheme.Modules.toPresheaf (Proj PS)).map
          (negativeTwistTrivializationHom K i m)).app
            (op (cechBasicOpen K n f))) s).1
        (cechGenericPoint K n f)).val :=
      congrArg (fun r => (r.1 (cechGenericPoint K n f)).val) hchart
    _ = _ := negativeTwistTrivializationHom_apply_val K i m
      (cechBasicOpen K n f) s (cechGenericPoint K n f)


lemma chartAway_cross_mul
    (m : ℕ) (i : Fin 4)
    (hdiv : MvPolynomial.X (R := K) i ∣ D)
    (j : Fin 4) (hdivj : MvPolynomial.X (R := K) j ∣ D)
    (s : Γ(sheafOfModules PS m, cechBasicOpen K n f)) :
    (chartAway K n f m i hdiv s).val *
        algebraMap S (Localization.Away D)
          ((degreeOnePower PS (p3Coordinate K j) m : PS m) : S) =
      (chartAway K n f m j hdivj s).val *
        algebraMap S (Localization.Away D)
          ((degreeOnePower PS (p3Coordinate K i) m : PS m) : S) := by
  apply genericLocalizationMap_injective K n f
  rw [map_mul, map_mul,
    genericLocalizationMap_chartAway K n f m i hdiv s,
    genericLocalizationMap_chartAway K n f m j hdivj s,
    genericLocalizationMap_algebraMap K n f,
    genericLocalizationMap_algebraMap K n f]
  change
    algebraMap S (Fiber PS (p3GenericPoint K))
          ((degreeOnePower PS (p3Coordinate K i) m : PS m) : S) *
        s.1 (cechGenericPoint K n f) *
      algebraMap S (Fiber PS (p3GenericPoint K))
          ((degreeOnePower PS (p3Coordinate K j) m : PS m) : S) =
    algebraMap S (Fiber PS (p3GenericPoint K))
          ((degreeOnePower PS (p3Coordinate K j) m : PS m) : S) *
        s.1 (cechGenericPoint K n f) *
      algebraMap S (Fiber PS (p3GenericPoint K))
          ((degreeOnePower PS (p3Coordinate K i) m : PS m) : S)
  ring

lemma polynomialToLaurent_degreeOnePower (m : ℕ) (k : Fin 4) :
    polynomialToLaurent (K := K)
        ((degreeOnePower PS (p3Coordinate K k) m : PS m) : S) =
      AddMonoidAlgebra.single (positiveTwistShift m k) 1 := by
  simp only [degreeOnePower, p3Coordinate, map_pow, polynomialToLaurent_X,
    positiveTwistShift, coordinateExponent, AddMonoidAlgebra.single_pow, one_pow]

lemma positiveTwistShift_mul_twistShift (m : ℕ) (k : Fin 4) :
    AddMonoidAlgebra.single (positiveTwistShift m k) (1 : K) *
      AddMonoidAlgebra.single (twistShift m k) 1 = 1 := by
  rw [AddMonoidAlgebra.single_mul_single]
  simp [positiveTwistShift, twistShift, AddMonoidAlgebra.one_def]

lemma twistShift_mul_positiveTwistShift (m : ℕ) (k : Fin 4) :
    AddMonoidAlgebra.single (twistShift m k) (1 : K) *
      AddMonoidAlgebra.single (positiveTwistShift m k) 1 = 1 := by
  rw [mul_comm, positiveTwistShift_mul_twistShift K m k]

lemma twistAwayToLaurent_chart_independent
    (m : ℕ) (i : Fin 4)
    (hdiv : MvPolynomial.X (R := K) i ∣ D)
    (j : Fin 4) (hdivj : MvPolynomial.X (R := K) j ∣ D)
    (s : Γ(sheafOfModules PS m, cechBasicOpen K n f)) :
    awayToLaurent (K := K) n f (chartAway K n f m i hdiv s) *
        AddMonoidAlgebra.single (twistShift m i) 1 =
      awayToLaurent (K := K) n f (chartAway K n f m j hdivj s) *
        AddMonoidAlgebra.single (twistShift m j) 1 := by
  have hcross := chartAway_cross_mul K n f m i hdiv j hdivj s
  have hL := congrArg (localizationAwayToLaurent (K := K) n f) hcross
  simp only [map_mul, localizationAwayToLaurent_algebraMap,
    polynomialToLaurent_degreeOnePower K m] at hL
  let ai := awayToLaurent (K := K) n f (chartAway K n f m i hdiv s)
  let aj := awayToLaurent (K := K) n f (chartAway K n f m j hdivj s)
  let pi := AddMonoidAlgebra.single (positiveTwistShift m i) (1 : K)
  let pj := AddMonoidAlgebra.single (positiveTwistShift m j) (1 : K)
  let qi := AddMonoidAlgebra.single (twistShift m i) (1 : K)
  let qj := AddMonoidAlgebra.single (twistShift m j) (1 : K)
  change ai * qi = aj * qj
  change ai * pj = aj * pi at hL
  calc
    ai * qi = ai * qi * 1 := by rw [mul_one]
    _ = ai * qi * (pj * qj) := by
      rw [positiveTwistShift_mul_twistShift K m j]
    _ = (ai * pj) * qi * qj := by ring
    _ = (aj * pi) * qi * qj := by rw [hL]
    _ = aj * qj * (pi * qi) := by ring
    _ = aj * qj := by
      rw [positiveTwistShift_mul_twistShift K m i, mul_one]

end GenericEvaluation

end PfaffianDescent.TwistCechTerms
