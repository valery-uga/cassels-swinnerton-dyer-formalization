import PfaffianDescent.VoisinStandardOpenExtVanishing
import PfaffianDescent.VoisinPositiveTwistTriviality
noncomputable section
namespace PfaffianDescent.ProjectiveFiniteNative
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial Opposite TopologicalSpace
open ProjectiveNegativeTwist
open scoped BigOperators
universe u w
variable {σ : Type} [Fintype σ] [DecidableEq σ] [Nontrivial σ]
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "S" => MvPolynomial (σ) K
local notation "PS" => MvPolynomial.homogeneousSubmodule (σ) K
def finitePolynomialCoordinate (i : σ) : PS 1 :=
  ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X K i⟩

def finitePolynomialStandardOpen (i : σ) : Scheme.Opens (Proj PS) :=
  ProjectiveSpectrum.basicOpen PS (finitePolynomialCoordinate K i : S)

lemma finitePolynomialCoordinates_span_irrelevant :
    (HomogeneousIdeal.irrelevant PS).toIdeal ≤
      Ideal.span (Set.range fun i : σ => (finitePolynomialCoordinate K i : S)) := by
  rw [HomogeneousIdeal.toIdeal_irrelevant_le]
  intro n hn p hp
  have hpvars : p ∈ MvPolynomial.idealOfVars (σ) K := by
    rw [← pow_one (MvPolynomial.idealOfVars (σ) K),
      MvPolynomial.mem_pow_idealOfVars_iff]
    intro mon hmon
    have he : mon.degree = n := by
      simpa only [Finsupp.degree_apply] using
        (MvPolynomial.IsHomogeneous.degree_eq_sum_deg_support hp hmon).symm
    exact he ▸ hn
  change p ∈ Ideal.span (Set.range fun i : σ => MvPolynomial.X i)
  simpa only [MvPolynomial.idealOfVars] using hpvars

lemma finitePolynomialStandardOpen_iSup :
    ⨆ i : σ, finitePolynomialStandardOpen (K := K) i = ⊤ := by
  apply Proj.iSup_basicOpen_eq_top
  exact finitePolynomialCoordinates_span_irrelevant K

theorem projective_basicOpen_finset_inf
    {ι : Type w} (s : Finset ι) (f : ι → S) :
    AlgebraicGeometry.Proj.basicOpen PS (∏ i ∈ s, f i) =
      s.inf (fun i => AlgebraicGeometry.Proj.basicOpen PS (f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.prod_insert, ha, not_false_eq_true,
        Finset.inf_insert]
      rw [AlgebraicGeometry.Proj.basicOpen_mul, ih]

def finitePolynomialCechDenominator (n : ℕ) (f : Fin (n + 1) → σ) : S :=
  ∏ a, MvPolynomial.X (R := K) (f a)

theorem finitePolynomialCechDenominator_mem (n : ℕ) (f : Fin (n + 1) → σ) :
    finitePolynomialCechDenominator (K := K) n f ∈ PS (n + 1) := by
  simpa [finitePolynomialCechDenominator] using MvPolynomial.IsHomogeneous.prod
    (Finset.univ : Finset (Fin (n + 1)))
    (fun a ↦ MvPolynomial.X (R := K) (f a)) (fun _ ↦ (1 : ℕ))
    (fun a _ ↦ MvPolynomial.isHomogeneous_X K (f a))

theorem finitePolynomialCoordinate_zero_dvd_cechDenominator
    (n : ℕ) (f : Fin (n + 1) → σ) :
    MvPolynomial.X (R := K) (f 0) ∣ finitePolynomialCechDenominator (K := K) n f := by
  simpa [finitePolynomialCechDenominator] using
    (Finset.dvd_prod_of_mem
      (fun a : Fin (n + 1) ↦ MvPolynomial.X (R := K) (f a))
      (Finset.mem_univ (0 : Fin (n + 1))))

theorem finitePolynomialCechBasicOpen_eq_inf (n : ℕ) (f : Fin (n + 1) → σ) :
    AlgebraicGeometry.Proj.basicOpen PS
        (finitePolynomialCechDenominator (K := K) n f) =
      ⨅ a, finitePolynomialStandardOpen (K := K) (f a) := by
  change AlgebraicGeometry.Proj.basicOpen PS
      (∏ a, MvPolynomial.X (R := K) (f a)) =
    ⨅ a, AlgebraicGeometry.Proj.basicOpen PS
      (MvPolynomial.X (R := K) (f a))
  rw [← Finset.inf_univ_eq_iInf]
  simpa using projective_basicOpen_finset_inf (K := K)
    (Finset.univ : Finset (Fin (n + 1)))
    (fun a ↦ MvPolynomial.X (R := K) (f a))

noncomputable def finitePolynomialPositiveTwistOpenIsoUnit
    (U : Scheme.Opens (Proj PS)) (i : σ)
    (hU : U ≤ finitePolynomialStandardOpen (K := K) i) (m : ℕ) :
    (Scheme.Modules.restrictFunctor U.ι).obj (positiveSheafOfModules PS m) ≅
      SheafOfModules.unit (U : Scheme).ringCatSheaf := by
  let R := Scheme.Modules.restrictFunctor U.ι
  let s := degreeOnePower PS (finitePolynomialCoordinate K i) m
  let f₀ := positiveMulHomogeneous PS s 0
  let e : positiveSheafOfModules PS (0 + m) ≅
      positiveSheafOfModules PS m := eqToIso (by rw [zero_add])
  let f : positiveSheafOfModules PS 0 ⟶ positiveSheafOfModules PS m :=
    f₀ ≫ e.hom
  have hf₀ : IsIso (R.map f₀) := by
    dsimp only [f₀, s]
    apply restrict_map_isIso_of_stalk U
    intro x
    letI : (positivePointIdeal PS (U.ι x)).IsPrime :=
      ProjectiveSpectrum.isPrime (U.ι x)
    have hXi : (MvPolynomial.X i : S) ∈
        (positivePointIdeal PS (U.ι x)).primeCompl := by
      rw [Ideal.mem_primeCompl_iff]
      exact (ProjectiveSpectrum.mem_basicOpen PS
        (MvPolynomial.X i) (U.ι x)).mp (hU x.property)
    have hsx : (degreeOnePower PS (finitePolynomialCoordinate K i) m : S) ∈
        (positivePointIdeal PS (U.ι x)).primeCompl := by
      change (MvPolynomial.X i : S) ^ m ∈
        (positivePointIdeal PS (U.ι x)).primeCompl
      exact Submonoid.pow_mem _ hXi m
    change IsIso ((TopCat.Presheaf.stalkFunctor _ (U.ι x)).map
      (positiveMulHomogeneousPresheaf PS
        (degreeOnePower PS (finitePolynomialCoordinate K i) m) 0))
    apply positiveMulHomogeneous_stalkMap_isIso_of_mem_primeCompl_of_irrelevant_le_span
      PS (degreeOnePower PS (finitePolynomialCoordinate K i) m) 0 (U.ι x) hsx
    exact (finitePolynomialCoordinates_span_irrelevant K).trans (Ideal.span_mono (by
      rintro _ ⟨j, rfl⟩
      exact ⟨finitePolynomialCoordinate K j, rfl⟩))
  letI : IsIso (R.map f₀) := hf₀
  letI : IsIso (R.map f) := by
    dsimp only [f]
    rw [R.map_comp]
    infer_instance
  exact (asIso (R.map f)).symm ≪≫
    R.mapIso (positiveZeroTwistIso PS) ≪≫
    (R.mapIso (unitIsoZeroTwist PS)).symm ≪≫
    Scheme.Modules.restrictUnitIso U.ι

theorem basicOpenIsoAway_inv_natural
    (f g x : S) (d e : ℕ)
    (hf : f ∈ PS d) (hg : g ∈ PS e) (hd : 0 < d)
    (hx : x = f * g) :
    (AlgebraicGeometry.Proj PS).presheaf.map
        (homOfLE (AlgebraicGeometry.Proj.basicOpen_mono PS f x ⟨g, hx⟩)).op ≫
      (AlgebraicGeometry.Proj.basicOpenIsoAway PS x
        (hx ▸ SetLike.mul_mem_graded hf hg) (Nat.add_pos_left hd e)).inv =
    (AlgebraicGeometry.Proj.basicOpenIsoAway PS f hf hd).inv ≫
      CommRingCat.ofHom (HomogeneousLocalization.awayMap PS hg hx) := by
  rw [← cancel_mono (AlgebraicGeometry.Proj.basicOpenIsoAway PS x
    (hx ▸ SetLike.mul_mem_graded hf hg) (Nat.add_pos_left hd e)).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [AlgebraicGeometry.Proj.basicOpenIsoAway_hom]
  rw [AlgebraicGeometry.Proj.awayMap_awayToSection]
  rw [← AlgebraicGeometry.Proj.basicOpenIsoAway_hom PS f hf hd]
  simp

lemma restrictUnit_app_top_topIso
    (U : Scheme.Opens (Proj PS)) :
    ((Scheme.Modules.toPresheaf (U : Scheme)).map
        (Scheme.Modules.restrictUnitIso U.ι).hom).app (op ⊤) ≫
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).map
        U.topIso.hom =
      (moduleRestrictTopIso
        (SheafOfModules.unit (AlgebraicGeometry.Proj PS).ringCatSheaf) U).hom := by
  ext r
  simp only [Functor.comp_obj, Scheme.Modules.toPresheaf_obj,
    Scheme.Modules.restrictUnitIso, Functor.op_obj, Scheme.Opens.ι_appIso,
    Scheme.Opens.topIso_hom, eqToHom_op, moduleRestrictTopIso,
    Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom]
  rfl

lemma basicOpenIsoAway_inv_natural_addCommGrp
    (f g x : S) (d e : ℕ)
    (hf : f ∈ PS d) (hg : g ∈ PS e) (hd : 0 < d)
    (hx : x = f * g) :
    let forgetRing := forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat
    forgetRing.map ((AlgebraicGeometry.Proj PS).presheaf.map
        (homOfLE (AlgebraicGeometry.Proj.basicOpen_mono PS f x ⟨g, hx⟩)).op) ≫
      forgetRing.map (AlgebraicGeometry.Proj.basicOpenIsoAway PS x
        (hx ▸ SetLike.mul_mem_graded hf hg) (Nat.add_pos_left hd e)).inv =
    forgetRing.map (AlgebraicGeometry.Proj.basicOpenIsoAway PS f hf hd).inv ≫
      forgetRing.map
        (CommRingCat.ofHom (HomogeneousLocalization.awayMap PS hg hx)) := by
  dsimp only
  have h := congrArg
    (fun q => (forget₂ CommRingCat RingCat ⋙
      forget₂ RingCat AddCommGrpCat).map q)
    (basicOpenIsoAway_inv_natural K f g x d e hf hg hd hx)
  simpa only [Functor.map_comp] using h

lemma moduleRestrictTopIso_local_map
    {M N : (Proj PS).Modules} (t : M ⟶ N)
    (U : Scheme.Opens (Proj PS)) :
    ((Scheme.Modules.toPresheaf (U : Scheme)).map
      ((Scheme.Modules.restrictFunctor U.ι).map t)).app (op ⊤) =
      (moduleRestrictTopIso M U).hom ≫
        ((Scheme.Modules.toPresheaf (Proj PS)).map t).app (op U) ≫
        (moduleRestrictTopIso N U).inv := by
  rw [moduleRestrictTopIso_naturality t U]
  simp

lemma positiveZeroAddCast_apply_val
    (m : ℕ) (U : (Scheme.Opens (Proj PS))ᵒᵖ)
    (z : (positiveSheafOfModules PS (0 + m)).val.obj U)
    (x : U.unop) :
    (((eqToIso (by rw [zero_add]) :
      positiveSheafOfModules PS (0 + m) ≅
        positiveSheafOfModules PS m).hom.val.app U z).1 x) = z.1 x := by
  let p : positiveSheafOfModules PS (0 + m) =
      positiveSheafOfModules PS m :=
    congrArg (positiveSheafOfModules PS) (Nat.zero_add m)
  change ((((eqToHom p : positiveSheafOfModules PS (0 + m) ⟶
      positiveSheafOfModules PS m).val.app U) z).1 x) = z.1 x
  have h :
      (((Scheme.Modules.toPresheaf (Proj PS)).map
        (eqToHom p)).app U z) ≍ z := by
    have hmor :
        (eqToHom p : positiveSheafOfModules PS (0 + m) ⟶
          positiveSheafOfModules PS m) ≍
          𝟙 (positiveSheafOfModules PS (0 + m)) :=
      eqToHom_heq_id_dom _ _ _
    have happ :
        ((Scheme.Modules.toPresheaf (Proj PS)).map (eqToHom p)).app U ≍
          ((Scheme.Modules.toPresheaf (Proj PS)).map
            (𝟙 (positiveSheafOfModules PS (0 + m)))).app U := by
      congr <;> exact (Nat.zero_add m).symm
    have hout :
        (((Scheme.Modules.toPresheaf (Proj PS)).map
          (eqToHom p)).app U) z ≍
        (((Scheme.Modules.toPresheaf (Proj PS)).map
          (𝟙 (positiveSheafOfModules PS (0 + m)))).app U) z := by
      congr <;> simp only [Nat.zero_add]
    have hid :
        (((Scheme.Modules.toPresheaf (Proj PS)).map
          (𝟙 (positiveSheafOfModules PS (0 + m)))).app U) z = z := by
      rfl
    exact hout.trans (heq_of_eq hid)
  have hcoe :
      (((((Scheme.Modules.toPresheaf (Proj PS)).map
        (eqToHom p)).app U) z).1) = z.1 :=
    (Subtype.heq_iff_coe_eq (fun q => by simp only [zero_add])).mp h
  exact congrFun hcoe x

lemma restrictUnit_inv_comp_moduleRestrictTop
    (U : Scheme.Opens (Proj PS)) :
    (((Scheme.Modules.toPresheaf (U : Scheme)).map
      (Scheme.Modules.restrictUnitIso U.ι).inv).app (op ⊤)) ≫
      (moduleRestrictTopIso
        (SheafOfModules.unit (Proj PS).ringCatSheaf) U).hom =
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).map
        U.topIso.hom := by
  let e := ((Scheme.Modules.toPresheaf (U : Scheme)).mapIso
    (Scheme.Modules.restrictUnitIso U.ι)).app (op ⊤)
  have h := restrictUnit_app_top_topIso K U
  change e.inv ≫
      (moduleRestrictTopIso
        (SheafOfModules.unit (Proj PS).ringCatSheaf) U).hom = _
  rw [← h]
  change e.inv ≫ e.hom ≫ _ = _
  exact e.inv_hom_id_assoc _

noncomputable def finitePolynomialPositiveTwistSectionsIsoUnit
    (U : Scheme.Opens (Proj PS)) (i : σ)
    (hU : U ≤ finitePolynomialStandardOpen (K := K) i) (m : ℕ) :
    Γ(positiveSheafOfModules PS m, U) ≅
      AddCommGrpCat.of Γ((U : Scheme), ⊤) := by
  let e := finitePolynomialPositiveTwistOpenIsoUnit K U i hU m
  exact (moduleRestrictTopIso (positiveSheafOfModules PS m) U).symm ≪≫
    ((Scheme.Modules.toPresheaf (U : Scheme)).mapIso e).app (op ⊤)

lemma finitePolynomialPositiveTwistSectionsIsoUnit_inv_decompose
    (U : Scheme.Opens (Proj PS)) (i : σ)
    (hU : U ≤ finitePolynomialStandardOpen (K := K) i) (m : ℕ) :
    let e := finitePolynomialPositiveTwistOpenIsoUnit K U i hU m
    (finitePolynomialPositiveTwistSectionsIsoUnit K U i hU m).inv =
      (((Scheme.Modules.toPresheaf (U : Scheme)).mapIso e).app (op ⊤)).inv ≫
        (moduleRestrictTopIso (positiveSheafOfModules PS m) U).hom := by
  dsimp only
  rfl

lemma finitePolynomialPositiveTwistSectionsIsoUnit_inv
    (U : Scheme.Opens (Proj PS)) (i : σ)
    (hU : U ≤ finitePolynomialStandardOpen (K := K) i) (m : ℕ) :
    let F := forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat
    let a := degreeOnePower PS (finitePolynomialCoordinate K i) m
    let eadd : positiveSheafOfModules PS (0 + m) ≅
        positiveSheafOfModules PS m := eqToIso (by rw [zero_add])
    let f : positiveSheafOfModules PS 0 ⟶ positiveSheafOfModules PS m :=
      positiveMulHomogeneous PS a 0 ≫ eadd.hom
    (finitePolynomialPositiveTwistSectionsIsoUnit K U i hU m).inv =
      F.map U.topIso.hom ≫
        ((Scheme.Modules.toPresheaf (Proj PS)).map
          (unitToZeroTwist PS)).app (op U) ≫
        ((Scheme.Modules.toPresheaf (Proj PS)).map
          (zeroTwistToPositiveZero PS)).app (op U) ≫
        ((Scheme.Modules.toPresheaf (Proj PS)).map f).app (op U) := by
  dsimp only
  let R := Scheme.Modules.restrictFunctor U.ι
  let a := degreeOnePower PS (finitePolynomialCoordinate K i) m
  let f₀ := positiveMulHomogeneous PS a 0
  let eadd : positiveSheafOfModules PS (0 + m) ≅
      positiveSheafOfModules PS m := eqToIso (by rw [zero_add])
  let f : positiveSheafOfModules PS 0 ⟶ positiveSheafOfModules PS m :=
    f₀ ≫ eadd.hom
  have hf₀ : IsIso (R.map f₀) := by
    dsimp only [f₀, a]
    apply restrict_map_isIso_of_stalk U
    intro x
    letI : (positivePointIdeal PS (U.ι x)).IsPrime :=
      ProjectiveSpectrum.isPrime (U.ι x)
    have hXi : (MvPolynomial.X i : S) ∈
        (positivePointIdeal PS (U.ι x)).primeCompl := by
      rw [Ideal.mem_primeCompl_iff]
      exact (ProjectiveSpectrum.mem_basicOpen PS
        (MvPolynomial.X i) (U.ι x)).mp (hU x.property)
    have hsx : (degreeOnePower PS (finitePolynomialCoordinate K i) m : S) ∈
        (positivePointIdeal PS (U.ι x)).primeCompl := by
      change (MvPolynomial.X i : S) ^ m ∈
        (positivePointIdeal PS (U.ι x)).primeCompl
      exact Submonoid.pow_mem _ hXi m
    change IsIso ((TopCat.Presheaf.stalkFunctor _ (U.ι x)).map
      (positiveMulHomogeneousPresheaf PS
        (degreeOnePower PS (finitePolynomialCoordinate K i) m) 0))
    apply positiveMulHomogeneous_stalkMap_isIso_of_mem_primeCompl_of_irrelevant_le_span
      PS (degreeOnePower PS (finitePolynomialCoordinate K i) m) 0 (U.ι x) hsx
    exact (finitePolynomialCoordinates_span_irrelevant K).trans (Ideal.span_mono (by
      rintro _ ⟨j, rfl⟩
      exact ⟨finitePolynomialCoordinate K j, rfl⟩))
  letI : IsIso (R.map f₀) := hf₀
  letI : IsIso (R.map f) := by
    dsimp only [f]
    rw [R.map_comp]
    infer_instance
  rw [finitePolynomialPositiveTwistSectionsIsoUnit_inv_decompose K U i hU m]
  let e := finitePolynomialPositiveTwistOpenIsoUnit K U i hU m
  change ((Scheme.Modules.toPresheaf (U : Scheme)).map e.inv).app (op ⊤) ≫
      (moduleRestrictTopIso (positiveSheafOfModules PS m) U).hom = _
  have heinv : e.inv =
      (((Scheme.Modules.restrictUnitIso U.ι).inv ≫
          R.map (unitIsoZeroTwist PS).hom) ≫
        R.map (positiveZeroTwistIso PS).inv) ≫ R.map f := by
    dsimp only [e, finitePolynomialPositiveTwistOpenIsoUnit]
    rfl
  rw [heinv]
  rw [schemeModulesToPresheaf_map_comp_app
    (((Scheme.Modules.restrictUnitIso U.ι).inv ≫
      R.map (unitIsoZeroTwist PS).hom) ≫
      R.map (positiveZeroTwistIso PS).inv) (R.map f) (op ⊤),
    schemeModulesToPresheaf_map_comp_app
      ((Scheme.Modules.restrictUnitIso U.ι).inv ≫
        R.map (unitIsoZeroTwist PS).hom)
      (R.map (positiveZeroTwistIso PS).inv) (op ⊤),
    schemeModulesToPresheaf_map_comp_app
      (Scheme.Modules.restrictUnitIso U.ι).inv
      (R.map (unitIsoZeroTwist PS).hom) (op ⊤)]
  have hunit : (unitIsoZeroTwist PS).hom = unitToZeroTwist PS := by
    dsimp only [unitIsoZeroTwist]
    rfl
  have hzero : (positiveZeroTwistIso PS).inv =
      zeroTwistToPositiveZero PS := rfl
  rw [hunit, hzero]
  rw [moduleRestrictTopIso_local_map K (unitToZeroTwist PS) U,
    moduleRestrictTopIso_local_map K (zeroTwistToPositiveZero PS) U,
    moduleRestrictTopIso_local_map K f U]
  exact cancel_three_iso_conjugations
    (((Scheme.Modules.toPresheaf (U : Scheme)).map
      (Scheme.Modules.restrictUnitIso U.ι).inv).app (op ⊤))
    (moduleRestrictTopIso
      (SheafOfModules.unit (Proj PS).ringCatSheaf) U).hom
    (((Scheme.Modules.toPresheaf (Proj PS)).map
      (unitToZeroTwist PS)).app (op U))
    (moduleRestrictTopIso (sheafOfModules PS 0) U)
    (((Scheme.Modules.toPresheaf (Proj PS)).map
      (zeroTwistToPositiveZero PS)).app (op U))
    (moduleRestrictTopIso (positiveSheafOfModules PS 0) U)
    (((Scheme.Modules.toPresheaf (Proj PS)).map f).app (op U))
    (moduleRestrictTopIso (positiveSheafOfModules PS m) U)
    ((forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).map
      U.topIso.hom)
    (restrictUnit_inv_comp_moduleRestrictTop K U)

lemma finitePolynomialPositiveTwistSectionsIsoUnit_inv_apply_val
    (U : Scheme.Opens (Proj PS)) (i : σ)
    (hU : U ≤ finitePolynomialStandardOpen (K := K) i) (m : ℕ)
    (r : Γ((U : Scheme), ⊤)) (x : U) :
    ((finitePolynomialPositiveTwistSectionsIsoUnit K U i hU m).inv r).1 x =
      algebraMap S (PositiveFiber PS x.1)
          ((degreeOnePower PS (finitePolynomialCoordinate K i) m : PS m) : S) *
        ((((forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).map
          U.topIso.hom) r).1 x).val := by
  rw [finitePolynomialPositiveTwistSectionsIsoUnit_inv K U i hU m]
  let F := forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat
  let q := F.map U.topIso.hom r
  let z₀ := ((Scheme.Modules.toPresheaf (Proj PS)).map
    (unitToZeroTwist PS)).app (op U) q
  let p₀ := ((Scheme.Modules.toPresheaf (Proj PS)).map
    (zeroTwistToPositiveZero PS)).app (op U) z₀
  let zm := (positiveMulHomogeneous PS
    (degreeOnePower PS (finitePolynomialCoordinate K i) m) 0).val.app (op U) p₀
  let eadd : positiveSheafOfModules PS (0 + m) ≅
      positiveSheafOfModules PS m := eqToIso (by rw [zero_add])
  change (((eadd.hom.val.app (op U)) zm).1 x) = _
  rw [positiveZeroAddCast_apply_val K m (op U) zm x]
  change algebraMap S (PositiveFiber PS x.1)
      ((degreeOnePower PS (finitePolynomialCoordinate K i) m : PS m) : S) * p₀.1 x = _
  rfl

noncomputable def finitePolynomialPositiveTwistSectionsIsoStructure
    (U : Scheme.Opens (Proj PS)) (i : σ)
    (hU : U ≤ finitePolynomialStandardOpen (K := K) i) (m : ℕ) :
    Γ(positiveSheafOfModules PS m, U) ≅
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).obj
        Γ(Proj PS, U) :=
  finitePolynomialPositiveTwistSectionsIsoUnit K U i hU m ≪≫
    (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).mapIso U.topIso

noncomputable def finitePolynomialPositiveTwistTrivializationInvHom
    (i : σ) (m : ℕ) :
    SheafOfModules.unit (Proj PS).ringCatSheaf ⟶
      positiveSheafOfModules PS m :=
  let a := degreeOnePower PS (finitePolynomialCoordinate K i) m
  let eadd : positiveSheafOfModules PS (0 + m) ≅
      positiveSheafOfModules PS m := eqToIso (by rw [zero_add])
  unitToZeroTwist PS ≫ zeroTwistToPositiveZero PS ≫
    (positiveMulHomogeneous PS a 0 ≫ eadd.hom)

lemma finitePolynomialPositiveTwistSectionsIsoStructure_inv
    (U : Scheme.Opens (Proj PS)) (i : σ)
    (hU : U ≤ finitePolynomialStandardOpen (K := K) i) (m : ℕ) :
    (finitePolynomialPositiveTwistSectionsIsoStructure K U i hU m).inv =
      ((Scheme.Modules.toPresheaf (Proj PS)).map
        (finitePolynomialPositiveTwistTrivializationInvHom K i m)).app (op U) := by
  let F := forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat
  let a := degreeOnePower PS (finitePolynomialCoordinate K i) m
  let eadd : positiveSheafOfModules PS (0 + m) ≅
      positiveSheafOfModules PS m := eqToIso (by rw [zero_add])
  let f : positiveSheafOfModules PS 0 ⟶ positiveSheafOfModules PS m :=
    positiveMulHomogeneous PS a 0 ≫ eadd.hom
  change F.map U.topIso.inv ≫
      (finitePolynomialPositiveTwistSectionsIsoUnit K U i hU m).inv = _
  rw [finitePolynomialPositiveTwistSectionsIsoUnit_inv K U i hU m]
  change F.map U.topIso.inv ≫
      F.map U.topIso.hom ≫
      ((Scheme.Modules.toPresheaf (Proj PS)).map
        (unitToZeroTwist PS)).app (op U) ≫
      ((Scheme.Modules.toPresheaf (Proj PS)).map
        (zeroTwistToPositiveZero PS)).app (op U) ≫
      ((Scheme.Modules.toPresheaf (Proj PS)).map f).app (op U) = _
  rw [← Category.assoc, ← F.map_comp]
  simp only [Iso.inv_hom_id, Functor.map_id, Category.id_comp]
  change _ = ((Scheme.Modules.toPresheaf (Proj PS)).map
    ((unitToZeroTwist PS ≫ zeroTwistToPositiveZero PS) ≫ f)).app (op U)
  rw [schemeModulesToPresheaf_map_comp_app
      (unitToZeroTwist PS ≫ zeroTwistToPositiveZero PS) f (op U),
    schemeModulesToPresheaf_map_comp_app
      (unitToZeroTwist PS) (zeroTwistToPositiveZero PS) (op U)]
  dsimp only [f]
  rw [schemeModulesToPresheaf_map_comp_app
    (positiveMulHomogeneous PS a 0) eadd.hom (op U)]
  simp only [Category.assoc] <;> rfl

lemma finitePolynomialPositiveTwistSectionsIsoStructure_natural
    (U V : Scheme.Opens (Proj PS)) (hVU : V ≤ U) (i : σ)
    (hU : U ≤ finitePolynomialStandardOpen (K := K) i) (m : ℕ) :
    (positiveSheafOfModules PS m).presheaf.map (homOfLE hVU).op ≫
        (finitePolynomialPositiveTwistSectionsIsoStructure K V i (hVU.trans hU) m).hom =
      (finitePolynomialPositiveTwistSectionsIsoStructure K U i hU m).hom ≫
        (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).map
          ((Proj PS).presheaf.map (homOfLE hVU).op) := by
  let eU := finitePolynomialPositiveTwistSectionsIsoStructure K U i hU m
  let eV := finitePolynomialPositiveTwistSectionsIsoStructure K V i (hVU.trans hU) m
  let rP := (positiveSheafOfModules PS m).presheaf.map (homOfLE hVU).op
  let rO := (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).map
    ((Proj PS).presheaf.map (homOfLE hVU).op)
  have hinv : rO ≫ eV.inv = eU.inv ≫ rP := by
    rw [finitePolynomialPositiveTwistSectionsIsoStructure_inv K,
      finitePolynomialPositiveTwistSectionsIsoStructure_inv K]
    exact ((Scheme.Modules.toPresheaf (Proj PS)).map
      (finitePolynomialPositiveTwistTrivializationInvHom K i m)).naturality (homOfLE hVU).op
  apply (cancel_mono eV.inv).mp
  change (rP ≫ eV.hom) ≫ eV.inv = (eU.hom ≫ rO) ≫ eV.inv
  simp only [Category.assoc, eV.hom_inv_id, Category.comp_id]
  rw [hinv]
  simp

noncomputable def finitePolynomialPositiveTwistBasicOpenIsoAway
    (f : S) (d : ℕ) (hf : f ∈ PS d) (hd : 0 < d)
    (i : σ) (hdiv : MvPolynomial.X i ∣ f) (m : ℕ) :
    Γ(positiveSheafOfModules PS m,
        AlgebraicGeometry.Proj.basicOpen PS f) ≅
      AddCommGrpCat.of (HomogeneousLocalization.Away PS f) := by
  let U := AlgebraicGeometry.Proj.basicOpen PS f
  have hU : U ≤ finitePolynomialStandardOpen (K := K) i :=
    AlgebraicGeometry.Proj.basicOpen_mono PS
      (MvPolynomial.X i) f hdiv
  let F := forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat
  exact finitePolynomialPositiveTwistSectionsIsoUnit K U i hU m ≪≫
    F.mapIso U.topIso ≪≫
    F.mapIso (AlgebraicGeometry.Proj.basicOpenIsoAway PS f hf hd).symm

lemma finitePolynomialPositiveTwistBasicOpenIsoAway_hom
    (f : S) (d : ℕ) (hf : f ∈ PS d) (hd : 0 < d)
    (i : σ) (hdiv : MvPolynomial.X i ∣ f) (m : ℕ) :
    let U := AlgebraicGeometry.Proj.basicOpen PS f
    let hU : U ≤ finitePolynomialStandardOpen (K := K) i :=
      AlgebraicGeometry.Proj.basicOpen_mono PS (MvPolynomial.X i) f hdiv
    let F := forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat
    (finitePolynomialPositiveTwistBasicOpenIsoAway K f d hf hd i hdiv m).hom =
      (finitePolynomialPositiveTwistSectionsIsoStructure K U i hU m).hom ≫
        F.map (AlgebraicGeometry.Proj.basicOpenIsoAway PS f hf hd).inv := by
  rfl

theorem positiveTwistBasicOpenIsoAway_natural
    (f g x : S) (d e : ℕ)
    (hf : f ∈ PS d) (hg : g ∈ PS e) (hd : 0 < d)
    (hx : x = f * g) (i : σ) (hdiv : MvPolynomial.X i ∣ f) (m : ℕ) :
    (positiveSheafOfModules PS m).presheaf.map
        (homOfLE (AlgebraicGeometry.Proj.basicOpen_mono PS f x ⟨g, hx⟩)).op ≫
      (finitePolynomialPositiveTwistBasicOpenIsoAway K x (d + e)
        (hx ▸ SetLike.mul_mem_graded hf hg) (Nat.add_pos_left hd e) i
        (dvd_trans hdiv ⟨g, hx⟩) m).hom =
    (finitePolynomialPositiveTwistBasicOpenIsoAway K f d hf hd i hdiv m).hom ≫
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).map
        (CommRingCat.ofHom (HomogeneousLocalization.awayMap PS hg hx)) := by
  let Uf := AlgebraicGeometry.Proj.basicOpen PS f
  let Ux := AlgebraicGeometry.Proj.basicOpen PS x
  let hxf : Ux ≤ Uf :=
    AlgebraicGeometry.Proj.basicOpen_mono PS f x ⟨g, hx⟩
  let hfi : Uf ≤ finitePolynomialStandardOpen (K := K) i :=
    AlgebraicGeometry.Proj.basicOpen_mono PS (MvPolynomial.X i) f hdiv
  let hxi : Ux ≤ finitePolynomialStandardOpen (K := K) i := hxf.trans hfi
  let F := forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat
  let bx := F.map (AlgebraicGeometry.Proj.basicOpenIsoAway PS x
    (hx ▸ SetLike.mul_mem_graded hf hg) (Nat.add_pos_left hd e)).inv
  let bf := F.map
    (AlgebraicGeometry.Proj.basicOpenIsoAway PS f hf hd).inv
  let amap := F.map
    (CommRingCat.ofHom (HomogeneousLocalization.awayMap PS hg hx))
  rw [finitePolynomialPositiveTwistBasicOpenIsoAway_hom K,
    finitePolynomialPositiveTwistBasicOpenIsoAway_hom K]
  have htwist := finitePolynomialPositiveTwistSectionsIsoStructure_natural
    K Uf Ux hxf i hfi m
  have haway := basicOpenIsoAway_inv_natural_addCommGrp
    K f g x d e hf hg hd hx
  change (positiveSheafOfModules PS m).presheaf.map (homOfLE hxf).op ≫
      (finitePolynomialPositiveTwistSectionsIsoStructure K Ux i hxi m).hom ≫ bx =
    (finitePolynomialPositiveTwistSectionsIsoStructure K Uf i hfi m).hom ≫ bf ≫ amap
  rw [← Category.assoc, htwist]
  simp only [Category.assoc]
  rw [haway]

end PfaffianDescent.ProjectiveFiniteNative

end
