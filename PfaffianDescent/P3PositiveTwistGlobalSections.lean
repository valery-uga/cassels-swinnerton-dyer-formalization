import PfaffianDescent.VoisinPositiveTwistTriviality
import PfaffianDescent.VoisinTwistLaurent
import PfaffianDescent.VoisinTwistCechNaturality

noncomputable section

namespace PfaffianDescent.ProjectiveNegativeTwist

open CategoryTheory AlgebraicGeometry MvPolynomial Opposite TopologicalSpace
open LaurentLocalization TwistLaurent
open TwistCechTerms TwistCechTerms.GenericEvaluation
open scoped AddMonoidAlgebra

universe u

variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

@[simp] lemma p3GenericPoint_positivePointIdeal :
    positivePointIdeal PS (p3GenericPoint K) = ⊥ :=
  p3GenericPoint_pointIdeal K

section CommonBasicOpen

variable (n : ℕ) (f : Fin (n + 1) → Fin 4)
local notation "D" => p3CechDenominator (K := K) n f

lemma positiveGenericPowersLE :
    Submonoid.powers D ≤ Submonoid.comap
      (RingHom.id (MvPolynomial (Fin 4) K))
      (positivePointIdeal PS (p3GenericPoint K)).primeCompl := by
  intro x hx
  have hx' := genericPowersLE K n f hx
  simpa only [Submonoid.mem_comap, RingHom.id_apply,
    p3GenericPoint_positivePointIdeal] using hx'

/-- The localization map from a Cech denominator directly into the ambient
fiber used by the positive twist at the generic point. -/
noncomputable def positiveGenericLocalizationMap :
    Localization.Away D →+* PositiveFiber PS (p3GenericPoint K) :=
  IsLocalization.map (PositiveFiber PS (p3GenericPoint K))
    (RingHom.id (MvPolynomial (Fin 4) K))
    (positiveGenericPowersLE K n f)

lemma positiveGenericLocalizationMap_injective :
    Function.Injective (positiveGenericLocalizationMap K n f) := by
  exact IsLocalization.map_injective_of_injective'
    (Submonoid.powers D) (MvPolynomial (Fin 4) K)
    (PositiveFiber PS (p3GenericPoint K))
    (f := RingHom.id (MvPolynomial (Fin 4) K))
    (Rₘ := Localization.Away D)
    (N := (positivePointIdeal PS (p3GenericPoint K)).primeCompl)
    (positiveGenericPowersLE K n f)
    (by
      intro h
      exact h (Ideal.zero_mem (positivePointIdeal PS (p3GenericPoint K))))
    (fun _ _ h => h)

lemma positiveGenericLocalizationMap_algebraMap
    (x : MvPolynomial (Fin 4) K) :
    positiveGenericLocalizationMap K n f
        (algebraMap (MvPolynomial (Fin 4) K) (Localization.Away D) x) =
      algebraMap (MvPolynomial (Fin 4) K)
        (PositiveFiber PS (p3GenericPoint K)) x := by
  exact IsLocalization.map_eq (positiveGenericPowersLE K n f) x

lemma awayToSection_positiveGeneric_apply
    (z : HomogeneousLocalization.Away PS D) :
    (((ProjectiveSpectrum.Proj.awayToSection PS D).1 z).val
      ⟨p3GenericPoint K,
        p3GenericPoint_mem_basicOpen_cechDenominator K n f⟩).val =
      positiveGenericLocalizationMap K n f z.val := by
  dsimp only [p3GenericPoint]
  unfold positiveGenericLocalizationMap
  rw [AlgebraicGeometry.ProjectiveSpectrum.Proj.awayToSection_apply]
  rfl

/-- The degree-zero homogeneous-localization coordinate of a positive-twist
section on a Cech basic open, after division by the chart basis `X_i^m`. -/
noncomputable abbrev p3PositiveTwistChartAway
    (m : ℕ) (i : Fin 4)
    (hdiv : MvPolynomial.X (R := K) i ∣ D)
    (s : Γ(positiveSheafOfModules PS m, cechBasicOpen K n f)) :
    HomogeneousLocalization.Away PS D :=
  (p3PositiveTwistBasicOpenIsoAway K D (n + 1)
    (p3CechDenominator_mem (K := K) n f) (Nat.succ_pos n)
    i hdiv m).hom s

/-- Undoing the homogeneous-localization presentation of a positive chart
coordinate gives the ordinary structure-function supplied by the local
trivialization. -/
lemma awayToSection_p3PositiveTwistChartAway
    (m : ℕ) (i : Fin 4)
    (hdiv : MvPolynomial.X (R := K) i ∣ D)
    (s : Γ(positiveSheafOfModules PS m, cechBasicOpen K n f)) :
    (ProjectiveSpectrum.Proj.awayToSection PS D).hom
        (p3PositiveTwistChartAway K n f m i hdiv s) =
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).map
          (cechBasicOpen K n f).topIso.hom
        ((p3PositiveTwistSectionsIsoUnit K (cechBasicOpen K n f) i
          (AlgebraicGeometry.Proj.basicOpen_mono PS
            (MvPolynomial.X i) D hdiv) m).hom s) := by
  let U := cechBasicOpen K n f
  let e := AlgebraicGeometry.Proj.basicOpenIsoAway PS D
    (p3CechDenominator_mem (K := K) n f) (Nat.succ_pos n)
  change e.hom
      ((p3PositiveTwistBasicOpenIsoAway K D (n + 1)
        (p3CechDenominator_mem (K := K) n f) (Nat.succ_pos n)
        i hdiv m).hom s) = _
  change e.hom (e.inv
    ((forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).map
      U.topIso.hom
      ((p3PositiveTwistSectionsIsoUnit K U i
        (AlgebraicGeometry.Proj.basicOpen_mono PS
          (MvPolynomial.X i) D hdiv) m).hom s))) = _
  exact e.inv_hom_id_apply _

/-- At the generic point, a positive-twist section is its chart coordinate
multiplied by the chart basis `X_i^m`. -/
lemma genericLocalizationMap_p3PositiveTwistChartAway
    (m : ℕ) (i : Fin 4)
    (hdiv : MvPolynomial.X (R := K) i ∣ D)
    (s : Γ(positiveSheafOfModules PS m, cechBasicOpen K n f)) :
    s.1 (cechGenericPoint K n f) =
      algebraMap (MvPolynomial (Fin 4) K)
          (PositiveFiber PS (p3GenericPoint K))
          ((degreeOnePower PS (p3Coordinate K i) m : PS m) :
            MvPolynomial (Fin 4) K) *
        (((ProjectiveSpectrum.Proj.awayToSection PS D).1
          (p3PositiveTwistChartAway K n f m i hdiv s)).val
            (cechGenericPoint K n f)).val := by
  let U := cechBasicOpen K n f
  let hU := AlgebraicGeometry.Proj.basicOpen_mono PS
    (MvPolynomial.X i) D hdiv
  let r := (p3PositiveTwistSectionsIsoUnit K U i hU m).hom s
  have hinv := p3PositiveTwistSectionsIsoUnit_inv_apply_val K U i hU m r
    (cechGenericPoint K n f)
  have hcancel : (p3PositiveTwistSectionsIsoUnit K U i hU m).inv r = s := by
    exact (p3PositiveTwistSectionsIsoUnit K U i hU m).hom_inv_id_apply s
  rw [hcancel] at hinv
  rw [hinv]
  congr 1
  have haway := awayToSection_p3PositiveTwistChartAway K n f m i hdiv s
  have hfun :
      (ProjectiveSpectrum.Proj.awayToSection PS D).1
          (p3PositiveTwistChartAway K n f m i hdiv s) =
        (ProjectiveSpectrum.Proj.awayToSection PS D).hom
          (p3PositiveTwistChartAway K n f m i hdiv s) := rfl
  have haway' := haway.symm.trans hfun.symm
  simpa only [U, r] using
    congrArg (fun q => (q.1 (cechGenericPoint K n f)).val) haway'

/-- Two positive chart coordinates of the same section agree after each is
multiplied by its own chart basis. -/
lemma p3PositiveTwistChartAway_cross_mul
    (m : ℕ) (i : Fin 4)
    (hdiv : MvPolynomial.X (R := K) i ∣ D)
    (j : Fin 4) (hdivj : MvPolynomial.X (R := K) j ∣ D)
    (s : Γ(positiveSheafOfModules PS m, cechBasicOpen K n f)) :
    (p3PositiveTwistChartAway K n f m i hdiv s).val *
        algebraMap (MvPolynomial (Fin 4) K) (Localization.Away D)
          ((degreeOnePower PS (p3Coordinate K i) m : PS m) :
            MvPolynomial (Fin 4) K) =
      (p3PositiveTwistChartAway K n f m j hdivj s).val *
        algebraMap (MvPolynomial (Fin 4) K) (Localization.Away D)
          ((degreeOnePower PS (p3Coordinate K j) m : PS m) :
            MvPolynomial (Fin 4) K) := by
  apply positiveGenericLocalizationMap_injective K n f
  rw [map_mul, map_mul,
    positiveGenericLocalizationMap_algebraMap K n f,
    positiveGenericLocalizationMap_algebraMap K n f]
  have hi := genericLocalizationMap_p3PositiveTwistChartAway
    K n f m i hdiv s
  have hj := genericLocalizationMap_p3PositiveTwistChartAway
    K n f m j hdivj s
  have hgi := awayToSection_positiveGeneric_apply K n f
    (p3PositiveTwistChartAway K n f m i hdiv s)
  have hgj := awayToSection_positiveGeneric_apply K n f
    (p3PositiveTwistChartAway K n f m j hdivj s)
  change ((((ProjectiveSpectrum.Proj.awayToSection PS D).1
      (p3PositiveTwistChartAway K n f m i hdiv s)).val
        (cechGenericPoint K n f)).val) = _ at hgi
  change ((((ProjectiveSpectrum.Proj.awayToSection PS D).1
      (p3PositiveTwistChartAway K n f m j hdivj s)).val
        (cechGenericPoint K n f)).val) = _ at hgj
  have hsections :
      (((ProjectiveSpectrum.Proj.awayToSection PS D).1
          (p3PositiveTwistChartAway K n f m i hdiv s)).val
            (cechGenericPoint K n f)).val *
          algebraMap (MvPolynomial (Fin 4) K)
            (PositiveFiber PS (p3GenericPoint K))
            ((degreeOnePower PS (p3Coordinate K i) m : PS m) :
              MvPolynomial (Fin 4) K) =
        (((ProjectiveSpectrum.Proj.awayToSection PS D).1
          (p3PositiveTwistChartAway K n f m j hdivj s)).val
            (cechGenericPoint K n f)).val *
          algebraMap (MvPolynomial (Fin 4) K)
            (PositiveFiber PS (p3GenericPoint K))
            ((degreeOnePower PS (p3Coordinate K j) m : PS m) :
              MvPolynomial (Fin 4) K) := by
    calc
      _ = algebraMap (MvPolynomial (Fin 4) K)
            (PositiveFiber PS (p3GenericPoint K))
            ((degreeOnePower PS (p3Coordinate K i) m : PS m) :
              MvPolynomial (Fin 4) K) *
          (((ProjectiveSpectrum.Proj.awayToSection PS D).1
            (p3PositiveTwistChartAway K n f m i hdiv s)).val
              (cechGenericPoint K n f)).val := mul_comm _ _
      _ = s.1 (cechGenericPoint K n f) := hi.symm
      _ = algebraMap (MvPolynomial (Fin 4) K)
            (PositiveFiber PS (p3GenericPoint K))
            ((degreeOnePower PS (p3Coordinate K j) m : PS m) :
              MvPolynomial (Fin 4) K) *
          (((ProjectiveSpectrum.Proj.awayToSection PS D).1
            (p3PositiveTwistChartAway K n f m j hdivj s)).val
              (cechGenericPoint K n f)).val := hj
      _ = _ := mul_comm _ _
  rw [hgi, hgj] at hsections
  exact hsections

/-- Restoring the chart basis makes the Laurent representative of a
positive-twist section independent of the chosen coordinate. -/
lemma p3PositiveTwistChartLaurent_independent
    (m : ℕ) (i : Fin 4)
    (hdiv : MvPolynomial.X (R := K) i ∣ D)
    (j : Fin 4) (hdivj : MvPolynomial.X (R := K) j ∣ D)
    (s : Γ(positiveSheafOfModules PS m, cechBasicOpen K n f)) :
    awayToLaurent (K := K) n f
        (p3PositiveTwistChartAway K n f m i hdiv s) *
        AddMonoidAlgebra.single (positiveTwistShift m i) 1 =
      awayToLaurent (K := K) n f
        (p3PositiveTwistChartAway K n f m j hdivj s) *
        AddMonoidAlgebra.single (positiveTwistShift m j) 1 := by
  have hcross := p3PositiveTwistChartAway_cross_mul
    K n f m i hdiv j hdivj s
  have hL := congrArg (localizationAwayToLaurent (K := K) n f) hcross
  simp only [map_mul, localizationAwayToLaurent_algebraMap,
    polynomialToLaurent_degreeOnePower K m] at hL
  change (localizationAwayToLaurent (K := K) n f)
        (p3PositiveTwistChartAway K n f m i hdiv s).val *
        AddMonoidAlgebra.single (positiveTwistShift m i) 1 =
      (localizationAwayToLaurent (K := K) n f)
        (p3PositiveTwistChartAway K n f m j hdivj s).val *
        AddMonoidAlgebra.single (positiveTwistShift m j) 1
  exact hL

end CommonBasicOpen

set_option backward.isDefEq.respectTransparency false in
/-- Restricting a positive chart coordinate along a Cech face does not
change its Laurent expansion when the same coordinate is used on both
opens. -/
lemma p3PositiveTwistChartLaurent_restrict_face
    (m n : ℕ) (i : Fin (n + 2)) (f : Fin (n + 2) → Fin 4)
    (s : Γ(positiveSheafOfModules PS m,
      cechBasicOpen K n (deleteTuple i f))) :
    let hS := p3Coordinate_zero_dvd_cechDenominator
      (K := K) n (deleteTuple i f)
    let hx := p3CechDenominator_succ_eq_deleteTuple_mul
      (K := K) n i f
    let hST : cechBasicOpen K (n + 1) f ≤
        cechBasicOpen K n (deleteTuple i f) :=
      AlgebraicGeometry.Proj.basicOpen_mono PS
        (p3CechDenominator (K := K) n (deleteTuple i f))
        (p3CechDenominator (K := K) (n + 1) f) ⟨_, hx⟩
    let sT : Γ(positiveSheafOfModules PS m, cechBasicOpen K (n + 1) f) :=
      (positiveSheafOfModules PS m).presheaf.map (homOfLE hST).op s
    awayToLaurent (K := K) (n + 1) f
        (p3PositiveTwistChartAway K (n + 1) f m
          ((deleteTuple i f) 0) (dvd_trans hS ⟨_, hx⟩) sT) =
      awayToLaurent (K := K) n (deleteTuple i f)
        (p3PositiveTwistChartAway K n (deleteTuple i f) m
          ((deleteTuple i f) 0) hS s) := by
  dsimp only
  let del := deleteTuple i f
  let denS := p3CechDenominator (K := K) n del
  let denT := p3CechDenominator (K := K) (n + 1) f
  let hx : denT = denS * MvPolynomial.X (R := K) (f i) :=
    p3CechDenominator_succ_eq_deleteTuple_mul (K := K) n i f
  let hS := p3Coordinate_zero_dvd_cechDenominator (K := K) n del
  let hAlt : MvPolynomial.X (R := K) (del 0) ∣ denT :=
    dvd_trans hS ⟨_, hx⟩
  let hST : cechBasicOpen K (n + 1) f ≤ cechBasicOpen K n del :=
    AlgebraicGeometry.Proj.basicOpen_mono PS denS denT ⟨_, hx⟩
  let sT : Γ(positiveSheafOfModules PS m, cechBasicOpen K (n + 1) f) :=
    (positiveSheafOfModules PS m).presheaf.map (homOfLE hST).op s
  let zS := p3PositiveTwistChartAway K n del m (del 0) hS s
  let zT := p3PositiveTwistChartAway K (n + 1) f m (del 0) hAlt sT
  have hnat := positiveTwistBasicOpenIsoAway_natural K
    denS (MvPolynomial.X (R := K) (f i)) denT (n + 1) 1
    (p3CechDenominator_mem (K := K) n del)
    (coordinate_mem_degree_one (K := K) (f i)) (Nat.succ_pos n) hx
    (del 0) hS m
  have hres : zT = awayFaceMap (K := K) n i f zS := by
    have happ := congrArg (fun q => q s) hnat
    simp only [ConcreteCategory.comp_apply] at happ
    change _ = _
    convert happ using 1
    rfl
  change awayToLaurent (K := K) (n + 1) f zT =
    awayToLaurent (K := K) n del zS
  rw [hres, awayToLaurent_awayFaceMap]

/-- The face-restriction formula specialized to the compatible local values
of one global positive-twist section. -/
lemma p3PositiveTwistGlobalChartLaurent_restrict_face
    (m n : ℕ) (i : Fin (n + 2)) (f : Fin (n + 2) → Fin 4)
    (s : (positiveSheafOfModules PS m).sections) :
    awayToLaurent (K := K) (n + 1) f
        (p3PositiveTwistChartAway K (n + 1) f m
          ((deleteTuple i f) 0)
          (dvd_trans
            (p3Coordinate_zero_dvd_cechDenominator
              (K := K) n (deleteTuple i f))
            ⟨_, p3CechDenominator_succ_eq_deleteTuple_mul
              (K := K) n i f⟩)
          (PresheafOfModules.sections.eval s
            (op (cechBasicOpen K (n + 1) f)))) =
      awayToLaurent (K := K) n (deleteTuple i f)
        (p3PositiveTwistChartAway K n (deleteTuple i f) m
          ((deleteTuple i f) 0)
          (p3Coordinate_zero_dvd_cechDenominator
            (K := K) n (deleteTuple i f))
          (PresheafOfModules.sections.eval s
            (op (cechBasicOpen K n (deleteTuple i f))))) := by
  let hST : cechBasicOpen K (n + 1) f ≤
      cechBasicOpen K n (deleteTuple i f) :=
    AlgebraicGeometry.Proj.basicOpen_mono PS
      (p3CechDenominator (K := K) n (deleteTuple i f))
      (p3CechDenominator (K := K) (n + 1) f)
      ⟨_, p3CechDenominator_succ_eq_deleteTuple_mul (K := K) n i f⟩
  have hsec := PresheafOfModules.sections_property s (homOfLE hST).op
  have hsec' :
      (positiveSheafOfModules PS m).presheaf.map (homOfLE hST).op
          (PresheafOfModules.sections.eval s
            (op (cechBasicOpen K n (deleteTuple i f)))) =
        PresheafOfModules.sections.eval s
          (op (cechBasicOpen K (n + 1) f)) := hsec
  have hface := p3PositiveTwistChartLaurent_restrict_face K m n i f
    (PresheafOfModules.sections.eval s
      (op (cechBasicOpen K n (deleteTuple i f))))
  dsimp only at hface
  rw [hsec'] at hface
  exact hface

/-- Restriction of a global positive-twist section to a standard chart. -/
noncomputable def p3PositiveTwistRestrictGlobal
    (m : ℕ) (s : (positiveSheafOfModules PS m).sections) (i : Fin 4) :
    Γ(positiveSheafOfModules PS m, p3StandardOpen (K := K) i) :=
  (positiveModulePresheaf PS m).presheaf.map
    (homOfLE (show p3StandardOpen (K := K) i ≤ ⊤ from le_top)).op
    (PresheafOfModules.sections.eval s (op (⊤ : Opens (Proj PS))))

lemma p3PositiveTwistRestrictGlobal_eq_eval
    (m : ℕ) (s : (positiveSheafOfModules PS m).sections) (i : Fin 4) :
    p3PositiveTwistRestrictGlobal K m s i =
      PresheafOfModules.sections.eval s
        (op (p3StandardOpen (K := K) i)) := by
  exact PresheafOfModules.sections_property s
    (homOfLE (show p3StandardOpen (K := K) i ≤ ⊤ from le_top)).op

/-- The degree-zero chart coordinate of a global positive-twist section. -/
noncomputable def p3PositiveTwistGlobalChartAway
    (m : ℕ) (hm : 0 < m)
    (s : (positiveSheafOfModules PS m).sections) (i : Fin 4) :
    HomogeneousLocalization.Away PS (MvPolynomial.X i) :=
  (p3PositiveTwistStandardOpenIsoAway K i m hm).hom
    (p3PositiveTwistRestrictGlobal K m s i)

/-- The Laurent representative of a positive-twist section on a standard
chart, after restoring the chart basis `X_i^m`. -/
noncomputable def p3PositiveTwistGlobalCechChartBase
    (m n : ℕ) (f : Fin (n + 1) → Fin 4)
    (s : (positiveSheafOfModules PS m).sections) :
    LaurentLocalization.LaurentPolynomial K :=
  awayToLaurent (K := K) n f
    (p3PositiveTwistChartAway K n f m (f 0)
      (p3Coordinate_zero_dvd_cechDenominator (K := K) n f)
      (PresheafOfModules.sections.eval s (op (cechBasicOpen K n f))))

/-- The Laurent representative of a positive-twist section on a standard
chart, after restoring the chart basis `X_i^m`. -/
noncomputable def p3PositiveTwistGlobalChartLaurent
    (m : ℕ) (hm : 0 < m)
    (s : (positiveSheafOfModules PS m).sections) (i : Fin 4) :
    LaurentLocalization.LaurentPolynomial K :=
  p3PositiveTwistGlobalCechChartBase K m 0 ![i] s *
    AddMonoidAlgebra.single (positiveTwistShift m i) 1

/-- Every monomial in a positive-twist chart representative has the twist
degree, and any negative exponent is confined to that chart's inverted
coordinate. -/
theorem p3PositiveTwistGlobalChartLaurent_support
    (m : ℕ) (hm : 0 < m)
    (s : (positiveSheafOfModules PS m).sections) (i : Fin 4) :
    ∀ a ∈ (p3PositiveTwistGlobalChartLaurent K m hm s i).coeff.support,
      totalDegree a = (m : ℤ) ∧ negativeSupport a ⊆ ({i} : Set (Fin 4)) := by
  intro a ha
  let z : HomogeneousLocalization.Away PS
      (p3CechDenominator (K := K) 0 ![i]) :=
    p3PositiveTwistChartAway K 0 ![i] m (![i] 0)
      (p3Coordinate_zero_dvd_cechDenominator (K := K) 0 ![i])
      (PresheafOfModules.sections.eval s
        (op (cechBasicOpen K 0 ![i])))
  change a ∈ (p3PositiveTwistGlobalCechChartBase K m 0 ![i] s *
      AddMonoidAlgebra.single (positiveTwistShift m i) 1).coeff.support at ha
  change a ∈ (awayToLaurent (K := K) 0 ![i] z *
      AddMonoidAlgebra.single (positiveTwistShift m i) 1).coeff.support at ha
  obtain ⟨b, hb, rfl⟩ :=
    (TwistLaurent.mul_single_mem_support_iff (K := K)
      (awayToLaurent (K := K) 0 ![i] z)
      (positiveTwistShift m i) a).mp ha
  have hbase := awayToLaurent_support_properties (K := K) 0 ![i] z b hb
  constructor
  · rw [totalDegree_add, hbase.1,
      TwistLaurent.totalDegree_positiveTwistShift]
    simp
  · have hneg :=
      (TwistLaurent.negativeSupport_add_positiveTwistShift_subset m i b).trans
        hbase.2
    simpa using hneg

/-- The restored Laurent representatives of a global positive-twist section
agree on all four standard coordinate charts. -/
theorem p3PositiveTwistGlobalChartLaurent_eq
    (m : ℕ) (hm : 0 < m)
    (s : (positiveSheafOfModules PS m).sections) (i j : Fin 4) :
    p3PositiveTwistGlobalChartLaurent K m hm s i =
      p3PositiveTwistGlobalChartLaurent K m hm s j := by
  let pair : Fin 2 → Fin 4 := ![i, j]
  let faceI : Fin 2 := 1
  let faceJ : Fin 2 := 0
  have hdelI : deleteTuple faceI pair = ![i] := by
    funext k
    fin_cases k
    rfl
  have hdelJ : deleteTuple faceJ pair = ![j] := by
    funext k
    fin_cases k
    rfl
  have hi := p3PositiveTwistGlobalChartLaurent_restrict_face
    K m 0 faceI pair s
  have hj := p3PositiveTwistGlobalChartLaurent_restrict_face
    K m 0 faceJ pair s
  let kI : Fin 4 := (deleteTuple faceI pair) 0
  let kJ : Fin 4 := (deleteTuple faceJ pair) 0
  have hkI : kI = i := by
    change (deleteTuple faceI pair) 0 = i
    rw [hdelI]
    rfl
  have hkJ : kJ = j := by
    change (deleteTuple faceJ pair) 0 = j
    rw [hdelJ]
    rfl
  have hi' := congrArg (fun q => q *
    AddMonoidAlgebra.single (positiveTwistShift m kI) (1 : K)) hi
  have hj' := congrArg (fun q => q *
    AddMonoidAlgebra.single (positiveTwistShift m kJ) (1 : K)) hj
  change _ = p3PositiveTwistGlobalCechChartBase K m 0
    (deleteTuple faceI pair) s *
      AddMonoidAlgebra.single (positiveTwistShift m kI) 1 at hi'
  change _ = p3PositiveTwistGlobalCechChartBase K m 0
    (deleteTuple faceJ pair) s *
      AddMonoidAlgebra.single (positiveTwistShift m kJ) 1 at hj'
  have hbaseI := congrArg
    (fun t => p3PositiveTwistGlobalCechChartBase K m 0 t s) hdelI
  have hbaseJ := congrArg
    (fun t => p3PositiveTwistGlobalCechChartBase K m 0 t s) hdelJ
  have hind := p3PositiveTwistChartLaurent_independent K 1 pair m kI
    (dvd_trans
      (p3Coordinate_zero_dvd_cechDenominator
        (K := K) 0 (deleteTuple faceI pair))
      ⟨_, p3CechDenominator_succ_eq_deleteTuple_mul
        (K := K) 0 faceI pair⟩) kJ
    (dvd_trans
      (p3Coordinate_zero_dvd_cechDenominator
        (K := K) 0 (deleteTuple faceJ pair))
      ⟨_, p3CechDenominator_succ_eq_deleteTuple_mul
        (K := K) 0 faceJ pair⟩)
    (PresheafOfModules.sections.eval s (op (cechBasicOpen K 1 pair)))
  calc
    p3PositiveTwistGlobalChartLaurent K m hm s i =
        p3PositiveTwistGlobalCechChartBase K m 0
            (deleteTuple faceI pair) s *
          AddMonoidAlgebra.single (positiveTwistShift m kI) 1 := by
      rw [p3PositiveTwistGlobalChartLaurent, hbaseI, hkI]
    _ = awayToLaurent (K := K) 1 pair
          (p3PositiveTwistChartAway K 1 pair m kI
            (dvd_trans
              (p3Coordinate_zero_dvd_cechDenominator
                (K := K) 0 (deleteTuple faceI pair))
              ⟨_, p3CechDenominator_succ_eq_deleteTuple_mul
                (K := K) 0 faceI pair⟩)
            (PresheafOfModules.sections.eval s
              (op (cechBasicOpen K 1 pair)))) *
          AddMonoidAlgebra.single (positiveTwistShift m kI) 1 := hi'.symm
    _ = awayToLaurent (K := K) 1 pair
          (p3PositiveTwistChartAway K 1 pair m kJ
            (dvd_trans
              (p3Coordinate_zero_dvd_cechDenominator
                (K := K) 0 (deleteTuple faceJ pair))
              ⟨_, p3CechDenominator_succ_eq_deleteTuple_mul
                (K := K) 0 faceJ pair⟩)
            (PresheafOfModules.sections.eval s
              (op (cechBasicOpen K 1 pair)))) *
          AddMonoidAlgebra.single (positiveTwistShift m kJ) 1 := hind
    _ = p3PositiveTwistGlobalCechChartBase K m 0
            (deleteTuple faceJ pair) s *
          AddMonoidAlgebra.single (positiveTwistShift m kJ) 1 := hj'
    _ = p3PositiveTwistGlobalChartLaurent K m hm s j := by
      rw [p3PositiveTwistGlobalChartLaurent, hbaseJ, hkJ]

/-- The chart Laurent representative of the global section attached to a
homogeneous polynomial is the Laurent image of that polynomial. -/
theorem p3PositiveTwistGlobalChartLaurent_of_homogeneous
    (m : ℕ) (hm : 0 < m) (p : PS m) (i : Fin 4) :
    p3PositiveTwistGlobalChartLaurent K m hm
        (positiveGlobalSectionOfHomogeneous PS m p) i =
      polynomialToLaurent (K := K) (p : MvPolynomial (Fin 4) K) := by
  let t : Fin 1 → Fin 4 := ![i]
  let s := positiveGlobalSectionOfHomogeneous PS m p
  let z := p3PositiveTwistChartAway K 0 t m (t 0)
    (p3Coordinate_zero_dvd_cechDenominator (K := K) 0 t)
    (PresheafOfModules.sections.eval s (op (cechBasicOpen K 0 t)))
  have hval := genericLocalizationMap_p3PositiveTwistChartAway K 0 t m (t 0)
    (p3Coordinate_zero_dvd_cechDenominator (K := K) 0 t)
    (PresheafOfModules.sections.eval s (op (cechBasicOpen K 0 t)))
  have hgen := awayToSection_positiveGeneric_apply K 0 t z
  change ((((ProjectiveSpectrum.Proj.awayToSection PS
      (p3CechDenominator (K := K) 0 t)).1 z).val
        (cechGenericPoint K 0 t)).val) = _ at hgen
  change _ = _ *
    (((ProjectiveSpectrum.Proj.awayToSection PS
      (p3CechDenominator (K := K) 0 t)).1 z).val
        (cechGenericPoint K 0 t)).val at hval
  rw [hgen] at hval
  have hcross : z.val *
        algebraMap (MvPolynomial (Fin 4) K)
          (Localization.Away (p3CechDenominator (K := K) 0 t))
          ((degreeOnePower PS (p3Coordinate K (t 0)) m : PS m) :
            MvPolynomial (Fin 4) K) =
      algebraMap (MvPolynomial (Fin 4) K)
        (Localization.Away (p3CechDenominator (K := K) 0 t))
        (p : MvPolynomial (Fin 4) K) := by
    apply positiveGenericLocalizationMap_injective K 0 t
    rw [map_mul, positiveGenericLocalizationMap_algebraMap K 0 t,
      positiveGenericLocalizationMap_algebraMap K 0 t]
    change positiveGenericLocalizationMap K 0 t z.val *
        algebraMap (MvPolynomial (Fin 4) K)
          (PositiveFiber PS (p3GenericPoint K))
          ((degreeOnePower PS (p3Coordinate K (t 0)) m : PS m) :
            MvPolynomial (Fin 4) K) =
      algebraMap (MvPolynomial (Fin 4) K)
        (PositiveFiber PS (p3GenericPoint K))
        (p : MvPolynomial (Fin 4) K)
    calc
      _ = algebraMap (MvPolynomial (Fin 4) K)
            (PositiveFiber PS (p3GenericPoint K))
            ((degreeOnePower PS (p3Coordinate K (t 0)) m : PS m) :
              MvPolynomial (Fin 4) K) *
          positiveGenericLocalizationMap K 0 t z.val := mul_comm _ _
      _ = (PresheafOfModules.sections.eval s
            (op (cechBasicOpen K 0 t))).1 (cechGenericPoint K 0 t) := hval.symm
      _ = Localization.mk (p : MvPolynomial (Fin 4) K)
            ⟨1, Submonoid.one_mem _⟩ := rfl
      _ = _ := Localization.mk_one_eq_algebraMap _
  have hL := congrArg (localizationAwayToLaurent (K := K) 0 t) hcross
  simp only [map_mul, localizationAwayToLaurent_algebraMap,
    polynomialToLaurent_degreeOnePower K m] at hL
  change awayToLaurent (K := K) 0 t z *
      AddMonoidAlgebra.single (positiveTwistShift m (t 0)) 1 =
    polynomialToLaurent (K := K) (p : MvPolynomial (Fin 4) K) at hL
  simpa [p3PositiveTwistGlobalChartLaurent,
    p3PositiveTwistGlobalCechChartBase, t, s, z] using hL

/-- A Laurent exponent which can have a negative coordinate only at every
one of two distinct coordinate indices has no negative coordinates. -/
lemma negativeSupport_eq_empty_of_subset_singletons
    (a : LaurentLocalization.LaurentExponent)
    (h₀ : negativeSupport a ⊆ ({(0 : Fin 4)} : Set (Fin 4)))
    (h₁ : negativeSupport a ⊆ ({(1 : Fin 4)} : Set (Fin 4))) :
    negativeSupport a = ∅ := by
  ext j
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hj
  have hj₀ : j = 0 := by simpa using h₀ hj
  have hj₁ : j = 1 := by simpa using h₁ hj
  omega

/-- Once the Laurent representatives on all standard charts agree, their
common monomials are ordinary nonnegative monomials of degree `m`. -/
theorem p3PositiveTwist_commonLaurent_support
    (m : ℕ) (hm : 0 < m)
    (s : (positiveSheafOfModules PS m).sections)
    (g : LaurentLocalization.LaurentPolynomial K)
    (hg : ∀ i, p3PositiveTwistGlobalChartLaurent K m hm s i = g) :
    ∀ a ∈ g.coeff.support,
      totalDegree a = (m : ℤ) ∧ negativeSupport a = ∅ := by
  intro a ha
  have hsupport (i : Fin 4) :
      totalDegree a = (m : ℤ) ∧
        negativeSupport a ⊆ ({i} : Set (Fin 4)) := by
    apply p3PositiveTwistGlobalChartLaurent_support K m hm s i
    simpa [hg i] using ha
  exact ⟨(hsupport 0).1,
    negativeSupport_eq_empty_of_subset_singletons a
      (hsupport 0).2 (hsupport 1).2⟩

/-- Convert a Laurent exponent known to be nonnegative coordinatewise into
an ordinary multivariate-polynomial exponent. -/
def nonnegativeExponentToNat
    (a : LaurentLocalization.LaurentExponent) : Fin 4 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i ↦ Int.toNat (a i)

@[simp] lemma nonnegativeExponentToNat_apply
    (a : LaurentLocalization.LaurentExponent) (i : Fin 4) :
    nonnegativeExponentToNat a i = Int.toNat (a i) := rfl

lemma exponentToInt_nonnegativeExponentToNat
    (a : LaurentLocalization.LaurentExponent)
    (ha : negativeSupport a = ∅) :
    exponentToInt (nonnegativeExponentToNat a) = a := by
  ext i
  rw [exponentToInt_apply, nonnegativeExponentToNat_apply,
    Int.toNat_of_nonneg]
  by_contra hi
  have hineg : i ∈ negativeSupport a := lt_of_not_ge hi
  rw [ha] at hineg
  exact hineg

lemma nonnegativeExponentToNat_degree
    (a : LaurentLocalization.LaurentExponent) (m : ℕ)
    (hdegree : totalDegree a = (m : ℤ))
    (ha : negativeSupport a = ∅) :
    (nonnegativeExponentToNat a).degree = m := by
  have htotal := totalDegree_exponentToInt (nonnegativeExponentToNat a)
  rw [exponentToInt_nonnegativeExponentToNat a ha, hdegree] at htotal
  rw [Finsupp.degree_apply, ← finsupp_sum_eq_sum_support]
  exact_mod_cast htotal.symm

lemma nonnegativeLaurentMonomial_mem_homogeneous
    (a : LaurentLocalization.LaurentExponent) (c : K) (m : ℕ)
    (hdegree : totalDegree a = (m : ℤ))
    (ha : negativeSupport a = ∅) :
    MvPolynomial.monomial (nonnegativeExponentToNat a) c ∈ PS m := by
  rw [MvPolynomial.mem_homogeneousSubmodule]
  exact MvPolynomial.isHomogeneous_monomial c
    (nonnegativeExponentToNat_degree a m hdegree ha)

/-- The ordinary polynomial obtained by interpreting every nonnegative
Laurent exponent as a natural exponent. -/
noncomputable def polynomialOfNonnegativeLaurent
    (g : LaurentLocalization.LaurentPolynomial K) :
    MvPolynomial (Fin 4) K :=
  ∑ a ∈ g.coeff.support,
    MvPolynomial.monomial (nonnegativeExponentToNat a) (g.coeff a)

/-- A Laurent polynomial supported in nonnegative degree-`m` exponents is
the Laurent image of an actual homogeneous polynomial of degree `m`. -/
theorem polynomialOfNonnegativeLaurent_mem_and_map
    (g : LaurentLocalization.LaurentPolynomial K) (m : ℕ)
    (hg : ∀ a ∈ g.coeff.support,
      totalDegree a = (m : ℤ) ∧ negativeSupport a = ∅) :
    polynomialOfNonnegativeLaurent K g ∈ PS m ∧
      polynomialToLaurent (K := K) (polynomialOfNonnegativeLaurent K g) = g := by
  classical
  constructor
  · apply Submodule.sum_mem
    intro a ha
    exact nonnegativeLaurentMonomial_mem_homogeneous K a (g.coeff a) m
      (hg a ha).1 (hg a ha).2
  · unfold polynomialOfNonnegativeLaurent
    rw [map_sum]
    calc
      ∑ a ∈ g.coeff.support,
          polynomialToLaurent (K := K)
            (MvPolynomial.monomial (nonnegativeExponentToNat a) (g.coeff a)) =
          ∑ a ∈ g.coeff.support,
            AddMonoidAlgebra.single a (g.coeff a) := by
              apply Finset.sum_congr rfl
              intro a ha
              rw [polynomialToLaurent_monomial,
                exponentToInt_nonnegativeExponentToNat a (hg a ha).2]
      _ = g := by
        simpa [Finsupp.sum] using (AddMonoidAlgebra.sum_coeff_single g)

/-- If the four chart representatives of a global positive-twist section
agree, their common value is represented by an ordinary homogeneous
polynomial of the twist degree. -/
theorem exists_homogeneous_polynomial_of_positiveTwist_commonLaurent
    (m : ℕ) (hm : 0 < m)
    (s : (positiveSheafOfModules PS m).sections)
    (g : LaurentLocalization.LaurentPolynomial K)
    (hg : ∀ i, p3PositiveTwistGlobalChartLaurent K m hm s i = g) :
    ∃ p : PS m, polynomialToLaurent (K := K) (p : MvPolynomial (Fin 4) K) = g := by
  let p := polynomialOfNonnegativeLaurent K g
  have hp := polynomialOfNonnegativeLaurent_mem_and_map K g m
    (p3PositiveTwist_commonLaurent_support K m hm s g hg)
  exact ⟨⟨p, hp.1⟩, hp.2⟩

/-- Every global positive-twist section determines a homogeneous polynomial
with the same Laurent representative on every standard chart. -/
theorem exists_homogeneous_polynomial_of_positiveTwist
    (m : ℕ) (hm : 0 < m)
    (s : (positiveSheafOfModules PS m).sections) :
    ∃ p : PS m, ∀ i,
      polynomialToLaurent (K := K) (p : MvPolynomial (Fin 4) K) =
        p3PositiveTwistGlobalChartLaurent K m hm s i := by
  obtain ⟨p, hp⟩ :=
    exists_homogeneous_polynomial_of_positiveTwist_commonLaurent
      K m hm s (p3PositiveTwistGlobalChartLaurent K m hm s 0)
      (fun i => p3PositiveTwistGlobalChartLaurent_eq K m hm s i 0)
  exact ⟨p, fun i => hp.trans
    (p3PositiveTwistGlobalChartLaurent_eq K m hm s 0 i)⟩

lemma eq_of_mul_positiveTwistShift_eq
    (m : ℕ) (i : Fin 4)
    {a b : LaurentLocalization.LaurentPolynomial K}
    (h : a * AddMonoidAlgebra.single (positiveTwistShift m i) 1 =
      b * AddMonoidAlgebra.single (positiveTwistShift m i) 1) :
    a = b := by
  let p := AddMonoidAlgebra.single (positiveTwistShift m i) (1 : K)
  let q := AddMonoidAlgebra.single (twistShift m i) (1 : K)
  change a * p = b * p at h
  calc
    a = a * 1 := by rw [mul_one]
    _ = a * (p * q) := by rw [positiveTwistShift_mul_twistShift K m i]
    _ = (a * p) * q := by ring
    _ = (b * p) * q := by rw [h]
    _ = b * (p * q) := by ring
    _ = b := by rw [positiveTwistShift_mul_twistShift K m i, mul_one]

/-- Equality of restored Laurent representatives on one coordinate chart
implies equality of the two section restrictions to that chart. -/
lemma p3PositiveTwist_restrict_eq_of_chartLaurent_eq
    (m : ℕ) (hm : 0 < m)
    (s t : (positiveSheafOfModules PS m).sections) (i : Fin 4)
    (h : p3PositiveTwistGlobalChartLaurent K m hm s i =
      p3PositiveTwistGlobalChartLaurent K m hm t i) :
    PresheafOfModules.sections.eval s (op (cechBasicOpen K 0 ![i])) =
      PresheafOfModules.sections.eval t (op (cechBasicOpen K 0 ![i])) := by
  have hbase : p3PositiveTwistGlobalCechChartBase K m 0 ![i] s =
      p3PositiveTwistGlobalCechChartBase K m 0 ![i] t := by
    apply eq_of_mul_positiveTwistShift_eq K m i
    simpa only [p3PositiveTwistGlobalChartLaurent] using h
  have haway :
      p3PositiveTwistChartAway K 0 ![i] m (![i] 0)
          (p3Coordinate_zero_dvd_cechDenominator (K := K) 0 ![i])
          (PresheafOfModules.sections.eval s
            (op (cechBasicOpen K 0 ![i]))) =
        p3PositiveTwistChartAway K 0 ![i] m (![i] 0)
          (p3Coordinate_zero_dvd_cechDenominator (K := K) 0 ![i])
          (PresheafOfModules.sections.eval t
            (op (cechBasicOpen K 0 ![i]))) := by
    apply awayToLaurent_injective (K := K) 0 ![i]
    simpa only [p3PositiveTwistGlobalCechChartBase] using hbase
  let e := p3PositiveTwistBasicOpenIsoAway K
    (p3CechDenominator (K := K) 0 ![i]) 1
    (p3CechDenominator_mem (K := K) 0 ![i]) (by decide)
    (![i] 0) (p3Coordinate_zero_dvd_cechDenominator (K := K) 0 ![i]) m
  change e.hom (PresheafOfModules.sections.eval s
      (op (cechBasicOpen K 0 ![i]))) =
    e.hom (PresheafOfModules.sections.eval t
      (op (cechBasicOpen K 0 ![i]))) at haway
  have hinv := congrArg (fun q => e.inv q) haway
  have hinv' :
      e.inv (e.hom (PresheafOfModules.sections.eval s
        (op (cechBasicOpen K 0 ![i])))) =
      e.inv (e.hom (PresheafOfModules.sections.eval t
        (op (cechBasicOpen K 0 ![i])))) := hinv
  have hs := e.hom_inv_id_apply
    (PresheafOfModules.sections.eval s (op (cechBasicOpen K 0 ![i])))
  have ht := e.hom_inv_id_apply
    (PresheafOfModules.sections.eval t (op (cechBasicOpen K 0 ![i])))
  exact hs.symm.trans (hinv'.trans ht)

lemma p3CechSingleOpen_eq_standard (i : Fin 4) :
    cechBasicOpen K 0 ![i] = p3StandardOpen (K := K) i := by
  change AlgebraicGeometry.Proj.basicOpen PS
      (p3CechDenominator (K := K) 0 ![i]) =
    AlgebraicGeometry.Proj.basicOpen PS (MvPolynomial.X i)
  congr 1
  simp [p3CechDenominator]

lemma p3CechSingleOpen_iSup :
    ⨆ i : Fin 4, cechBasicOpen K 0 ![i] = ⊤ := by
  simp_rw [p3CechSingleOpen_eq_standard K]
  exact p3StandardOpen_iSup K

/-- Global positive-twist sections are determined by their four restored
Laurent chart representatives. -/
theorem p3PositiveTwist_global_eq_of_chartLaurent_eq
    (m : ℕ) (hm : 0 < m)
    (s t : (positiveSheafOfModules PS m).sections)
    (h : ∀ i, p3PositiveTwistGlobalChartLaurent K m hm s i =
      p3PositiveTwistGlobalChartLaurent K m hm t i) :
    s = t := by
  let M := positiveSheafOfModules PS m
  let G : TopCat.Sheaf AddCommGrpCat (Proj PS) :=
    (SheafOfModules.toSheaf (Proj PS).ringCatSheaf).obj M
  have htop : PresheafOfModules.sections.eval s
        (op (⊤ : Opens (Proj PS))) =
      PresheafOfModules.sections.eval t
        (op (⊤ : Opens (Proj PS))) := by
    apply G.eq_of_locally_eq'
      (fun i : Fin 4 => cechBasicOpen K 0 ![i])
      (⊤ : Opens (Proj PS))
      (fun _ => homOfLE le_top)
      (by rw [p3CechSingleOpen_iSup K])
    intro i
    change (positiveSheafOfModules PS m).presheaf.map
        (homOfLE (show cechBasicOpen K 0 ![i] ≤
          (⊤ : Opens (Proj PS)) from le_top)).op
          (PresheafOfModules.sections.eval s
            (op (⊤ : Opens (Proj PS)))) =
      (positiveSheafOfModules PS m).presheaf.map
        (homOfLE (show cechBasicOpen K 0 ![i] ≤
          (⊤ : Opens (Proj PS)) from le_top)).op
          (PresheafOfModules.sections.eval t
            (op (⊤ : Opens (Proj PS))))
    have hsres : (positiveSheafOfModules PS m).presheaf.map
          (homOfLE (show cechBasicOpen K 0 ![i] ≤
            (⊤ : Opens (Proj PS)) from le_top)).op
            (PresheafOfModules.sections.eval s
              (op (⊤ : Opens (Proj PS)))) =
        PresheafOfModules.sections.eval s
          (op (cechBasicOpen K 0 ![i])) :=
      PresheafOfModules.sections_property s _
    have htres : (positiveSheafOfModules PS m).presheaf.map
          (homOfLE (show cechBasicOpen K 0 ![i] ≤
            (⊤ : Opens (Proj PS)) from le_top)).op
            (PresheafOfModules.sections.eval t
              (op (⊤ : Opens (Proj PS)))) =
        PresheafOfModules.sections.eval t
          (op (cechBasicOpen K 0 ![i])) :=
      PresheafOfModules.sections_property t _
    rw [hsres, htres]
    exact p3PositiveTwist_restrict_eq_of_chartLaurent_eq K m hm s t i (h i)
  apply PresheafOfModules.sections_ext
  intro U
  let r := (positiveSheafOfModules PS m).presheaf.map
    (homOfLE (show U.unop ≤ (⊤ : Opens (Proj PS)) from le_top)).op
  have hsU := PresheafOfModules.sections_property s
    (homOfLE (show U.unop ≤ (⊤ : Opens (Proj PS)) from le_top)).op
  have htU := PresheafOfModules.sections_property t
    (homOfLE (show U.unop ≤ (⊤ : Opens (Proj PS)) from le_top)).op
  have hres : r (PresheafOfModules.sections.eval s
        (op (⊤ : Opens (Proj PS)))) =
      r (PresheafOfModules.sections.eval t
        (op (⊤ : Opens (Proj PS)))) := congrArg (fun q => r q) htop
  exact hsU.symm.trans (hres.trans htU)

/-- Homogeneous polynomials generate all global sections of every positive
twist on projective three-space. -/
theorem p3_positiveGlobalSectionOfHomogeneous_surjective
    (m : ℕ) (hm : 0 < m) :
    Function.Surjective (positiveGlobalSectionOfHomogeneous PS m) := by
  intro s
  obtain ⟨p, hp⟩ := exists_homogeneous_polynomial_of_positiveTwist K m hm s
  refine ⟨p, ?_⟩
  apply p3PositiveTwist_global_eq_of_chartLaurent_eq K m hm
  intro i
  exact (p3PositiveTwistGlobalChartLaurent_of_homogeneous K m hm p i).trans
    (hp i)

end PfaffianDescent.ProjectiveNegativeTwist
