import PfaffianDescent.PlaneNativeCechCover
/-! SOURCE ONLY / UNCHECKED: actual Fin3 positive and negative chart-section
isomorphisms and ordinary homogeneous-localization restriction naturality.
Each frame is constructed from the actual native sheaf morphism; no chart
comparison, cohomology or Euler outcome is assumed. -/
noncomputable section
namespace PfaffianDescent.ProjectivePlaneNative
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial Opposite
open TopologicalSpace AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "S" => MvPolynomial (Fin 3) K
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 3) K
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
def p2NegativeTwistSectionsIsoUnit
    (U : Scheme.Opens (Proj PS)) (i : Fin 3)
    (hU : U ≤ p2StandardOpen (K := K) i) (m : ℕ) :
    Γ(sheafOfModules PS m, U) ≅
      AddCommGrpCat.of Γ((U : Scheme), ⊤) := by
  let e := p2NegativeTwistOpenIsoUnit K U i hU m
  exact (moduleRestrictTopIso (sheafOfModules PS m) U).symm ≪≫
    ((Scheme.Modules.toPresheaf (U : Scheme)).mapIso e).app (op ⊤)

/-- On a homogeneous basic open contained in `D_+(X_i)`, sections of the
negative twist are identified with the degree-zero homogeneous localization.
The identification sends a section to its product with `X_i^m`. -/
def p2NegativeTwistBasicOpenIsoAway
    (f : S) (d : ℕ) (hf : f ∈ PS d) (hd : 0 < d)
    (i : Fin 3) (hdiv : MvPolynomial.X i ∣ f) (m : ℕ) :
    Γ(sheafOfModules PS m, AlgebraicGeometry.Proj.basicOpen PS f) ≅
      AddCommGrpCat.of (HomogeneousLocalization.Away PS f) := by
  let U := AlgebraicGeometry.Proj.basicOpen PS f
  have hU : U ≤ p2StandardOpen (K := K) i :=
    AlgebraicGeometry.Proj.basicOpen_mono PS
      (MvPolynomial.X i) f hdiv
  let F := forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat
  exact p2NegativeTwistSectionsIsoUnit K U i hU m ≪≫
    F.mapIso U.topIso ≪≫
    F.mapIso (AlgebraicGeometry.Proj.basicOpenIsoAway PS f hf hd).symm

/-- Naturality of the standard identification of projective basic-open
functions with degree-zero homogeneous localizations. -/
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

/-- Multiplication by `X_i^m`, followed by the zero-twist/unit
identification, as one global sheaf morphism. -/
def negativeTwistTrivializationHom (i : Fin 3) (m : ℕ) :
    sheafOfModules PS m ⟶
      SheafOfModules.unit (AlgebraicGeometry.Proj PS).ringCatSheaf := by
  let s := degreeOnePower PS (p2Coordinate K i) m
  let f : sheafOfModules PS m ⟶ sheafOfModules PS 0 := by
    simpa using mulHomogeneous PS s 0
  exact f ≫ (unitIsoZeroTwist PS).inv

lemma p2NegativeTwistOpenIsoUnit_hom
    (U : Scheme.Opens (Proj PS)) (i : Fin 3)
    (hU : U ≤ p2StandardOpen (K := K) i) (m : ℕ) :
    (p2NegativeTwistOpenIsoUnit K U i hU m).hom =
      (Scheme.Modules.restrictFunctor U.ι).map
          (negativeTwistTrivializationHom K i m) ≫
        (Scheme.Modules.restrictUnitIso U.ι).hom := by
  dsimp [p2NegativeTwistOpenIsoUnit, negativeTwistTrivializationHom]
  rfl

lemma p2NegativeTwistOpenIsoUnit_app_top
    (U : Scheme.Opens (Proj PS)) (i : Fin 3)
    (hU : U ≤ p2StandardOpen (K := K) i) (m : ℕ) :
    (((Scheme.Modules.toPresheaf (U : Scheme)).mapIso
      (p2NegativeTwistOpenIsoUnit K U i hU m)).app (op ⊤)).hom =
      ((Scheme.Modules.toPresheaf (U : Scheme)).map
        ((Scheme.Modules.restrictFunctor U.ι).map
          (negativeTwistTrivializationHom K i m))).app (op ⊤) ≫
      ((Scheme.Modules.toPresheaf (U : Scheme)).map
        (Scheme.Modules.restrictUnitIso U.ι).hom).app (op ⊤) := by
  change ((Scheme.Modules.toPresheaf (U : Scheme)).map
      (p2NegativeTwistOpenIsoUnit K U i hU m).hom).app (op ⊤) = _
  rw [p2NegativeTwistOpenIsoUnit_hom]
  exact schemeModulesToPresheaf_map_comp_app _ _ (op ⊤)

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

set_option backward.isDefEq.respectTransparency false in
/-- The hom of the chart-section isomorphism is the component of the single
global multiplication morphism. -/
theorem p2NegativeTwistSectionsIsoUnit_hom_topIso
    (U : Scheme.Opens (Proj PS)) (i : Fin 3)
    (hU : U ≤ p2StandardOpen (K := K) i) (m : ℕ) :
    (p2NegativeTwistSectionsIsoUnit K U i hU m).hom ≫
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).map
        U.topIso.hom =
      ((Scheme.Modules.toPresheaf (Proj PS)).map
        (negativeTwistTrivializationHom K i m)).app (op U) := by
  rw [moduleRestrictTopIso_naturality
    (negativeTwistTrivializationHom K i m) U]
  let eM := (moduleRestrictTopIso (sheafOfModules PS m) U).inv
  let b := (((Scheme.Modules.toPresheaf (U : Scheme)).mapIso
    (p2NegativeTwistOpenIsoUnit K U i hU m)).app (op ⊤)).hom
  let a := ((Scheme.Modules.toPresheaf (U : Scheme)).map
    ((Scheme.Modules.restrictFunctor U.ι).map
      (negativeTwistTrivializationHom K i m))).app (op ⊤)
  let r := ((Scheme.Modules.toPresheaf (U : Scheme)).map
    (Scheme.Modules.restrictUnitIso U.ι).hom).app (op ⊤)
  let q := (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).map
    U.topIso.hom
  let eN := (moduleRestrictTopIso
    (SheafOfModules.unit (AlgebraicGeometry.Proj PS).ringCatSheaf) U).hom
  have hdef : (p2NegativeTwistSectionsIsoUnit K U i hU m).hom = eM ≫ b := rfl
  have hb : b = a ≫ r := p2NegativeTwistOpenIsoUnit_app_top K U i hU m
  have hr : r ≫ q = eN := restrictUnit_app_top_topIso K U
  rw [hdef, hb]
  change (eM ≫ a ≫ r) ≫ q = eM ≫ a ≫ eN
  simp only [Category.assoc]
  rw [hr]

/-- The chart trivialization, with values transported back to ambient
structure-sheaf sections. -/
def negativeTwistSectionsIsoStructure
    (U : Scheme.Opens (Proj PS)) (i : Fin 3)
    (hU : U ≤ p2StandardOpen (K := K) i) (m : ℕ) :
    Γ(sheafOfModules PS m, U) ≅
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).obj
        Γ(Proj PS, U) :=
  p2NegativeTwistSectionsIsoUnit K U i hU m ≪≫
    (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).mapIso U.topIso

/-- The twist trivialization by `X_i^m` commutes with restriction between
opens lying in the same coordinate chart. -/
theorem negativeTwistSectionsIsoStructure_natural
    (U V : Scheme.Opens (Proj PS)) (hVU : V ≤ U) (i : Fin 3)
    (hU : U ≤ p2StandardOpen (K := K) i) (m : ℕ) :
    (sheafOfModules PS m).presheaf.map (homOfLE hVU).op ≫
      (negativeTwistSectionsIsoStructure K V i (hVU.trans hU) m).hom =
    (negativeTwistSectionsIsoStructure K U i hU m).hom ≫
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).map
        ((AlgebraicGeometry.Proj PS).presheaf.map (homOfLE hVU).op) := by
  change (sheafOfModules PS m).presheaf.map (homOfLE hVU).op ≫
      ((p2NegativeTwistSectionsIsoUnit K V i (hVU.trans hU) m).hom ≫
        (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).map
          V.topIso.hom) =
    ((p2NegativeTwistSectionsIsoUnit K U i hU m).hom ≫
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).map
        U.topIso.hom) ≫
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).map
        ((AlgebraicGeometry.Proj PS).presheaf.map (homOfLE hVU).op)
  rw [p2NegativeTwistSectionsIsoUnit_hom_topIso]
  rw [p2NegativeTwistSectionsIsoUnit_hom_topIso]
  exact ((Scheme.Modules.toPresheaf (Proj PS)).map
    (negativeTwistTrivializationHom K i m)).naturality (homOfLE hVU).op

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

lemma p2NegativeTwistBasicOpenIsoAway_hom
    (f : S) (d : ℕ) (hf : f ∈ PS d) (hd : 0 < d)
    (i : Fin 3) (hdiv : MvPolynomial.X i ∣ f) (m : ℕ) :
    let U := AlgebraicGeometry.Proj.basicOpen PS f
    let hU : U ≤ p2StandardOpen (K := K) i :=
      AlgebraicGeometry.Proj.basicOpen_mono PS (MvPolynomial.X i) f hdiv
    let forgetRing := forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat
    (p2NegativeTwistBasicOpenIsoAway K f d hf hd i hdiv m).hom =
      (negativeTwistSectionsIsoStructure K U i hU m).hom ≫
        forgetRing.map (AlgebraicGeometry.Proj.basicOpenIsoAway PS f hf hd).inv := by
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Restriction from `D₊(f)` to `D₊(fg)` is carried by the concrete twist
section isomorphisms to the canonical homogeneous-localization map. -/
theorem negativeTwistBasicOpenIsoAway_natural
    (f g x : S) (d e : ℕ)
    (hf : f ∈ PS d) (hg : g ∈ PS e) (hd : 0 < d)
    (hx : x = f * g) (i : Fin 3) (hdiv : MvPolynomial.X i ∣ f) (m : ℕ) :
    (sheafOfModules PS m).presheaf.map
        (homOfLE (AlgebraicGeometry.Proj.basicOpen_mono PS f x ⟨g, hx⟩)).op ≫
      (p2NegativeTwistBasicOpenIsoAway K x (d + e)
        (hx ▸ SetLike.mul_mem_graded hf hg) (Nat.add_pos_left hd e) i
        (dvd_trans hdiv ⟨g, hx⟩) m).hom =
    (p2NegativeTwistBasicOpenIsoAway K f d hf hd i hdiv m).hom ≫
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).map
        (CommRingCat.ofHom (HomogeneousLocalization.awayMap PS hg hx)) := by
  let Uf := AlgebraicGeometry.Proj.basicOpen PS f
  let Ux := AlgebraicGeometry.Proj.basicOpen PS x
  let hxf : Ux ≤ Uf :=
    AlgebraicGeometry.Proj.basicOpen_mono PS f x ⟨g, hx⟩
  let hfi : Uf ≤ p2StandardOpen (K := K) i :=
    AlgebraicGeometry.Proj.basicOpen_mono PS (MvPolynomial.X i) f hdiv
  let hxi : Ux ≤ p2StandardOpen (K := K) i := hxf.trans hfi
  let forgetRing := forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat
  let bx := forgetRing.map (AlgebraicGeometry.Proj.basicOpenIsoAway PS x
    (hx ▸ SetLike.mul_mem_graded hf hg) (Nat.add_pos_left hd e)).inv
  let bf := forgetRing.map
    (AlgebraicGeometry.Proj.basicOpenIsoAway PS f hf hd).inv
  let amap := forgetRing.map
    (CommRingCat.ofHom (HomogeneousLocalization.awayMap PS hg hx))
  have hxHom := p2NegativeTwistBasicOpenIsoAway_hom K x (d + e)
    (hx ▸ SetLike.mul_mem_graded hf hg) (Nat.add_pos_left hd e) i
    (dvd_trans hdiv ⟨g, hx⟩) m
  have hfHom := p2NegativeTwistBasicOpenIsoAway_hom K f d hf hd i hdiv m
  rw [hxHom, hfHom]
  have htwist := negativeTwistSectionsIsoStructure_natural K Uf Ux hxf i hfi m
  have haway := basicOpenIsoAway_inv_natural_addCommGrp
    K f g x d e hf hg hd hx
  change (sheafOfModules PS m).presheaf.map (homOfLE hxf).op ≫
      (negativeTwistSectionsIsoStructure K Ux i hxi m).hom ≫ bx =
    (negativeTwistSectionsIsoStructure K Uf i hfi m).hom ≫ bf ≫ amap
  rw [← Category.assoc, htwist]
  simp only [Category.assoc]
  rw [haway]


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

/-- Pulling a function on an open subscheme back through the restricted-unit
isomorphism and then returning to ambient sections is the ordinary top-open
identification. -/
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


noncomputable def p2PositiveTwistStandardOpenIsoUnit
    (i : Fin 3) (m : ℕ) (hm : 0 < m) :
    (Scheme.Modules.restrictFunctor
      (p2StandardOpen (K := K) i).ι).obj (positiveSheafOfModules PS m) ≅
      SheafOfModules.unit
        (p2StandardOpen (K := K) i : Scheme).ringCatSheaf := by
  exact p2PositiveTwistOpenIsoUnit K (p2StandardOpen (K := K) i) i le_rfl m

/-- Sections of the positive twist on an open contained in `D₊(X_i)` are
identified with regular functions on that open by division by `X_i^m`. -/
noncomputable def p2PositiveTwistSectionsIsoUnit
    (U : Scheme.Opens (Proj PS)) (i : Fin 3)
    (hU : U ≤ p2StandardOpen (K := K) i) (m : ℕ) :
    Γ(positiveSheafOfModules PS m, U) ≅
      AddCommGrpCat.of Γ((U : Scheme), ⊤) := by
  let e := p2PositiveTwistOpenIsoUnit K U i hU m
  exact (moduleRestrictTopIso (positiveSheafOfModules PS m) U).symm ≪≫
    ((Scheme.Modules.toPresheaf (U : Scheme)).mapIso e).app (op ⊤)

lemma p2PositiveTwistSectionsIsoUnit_inv_decompose
    (U : Scheme.Opens (Proj PS)) (i : Fin 3)
    (hU : U ≤ p2StandardOpen (K := K) i) (m : ℕ) :
    let e := p2PositiveTwistOpenIsoUnit K U i hU m
    (p2PositiveTwistSectionsIsoUnit K U i hU m).inv =
      (((Scheme.Modules.toPresheaf (U : Scheme)).mapIso e).app (op ⊤)).inv ≫
        (moduleRestrictTopIso (positiveSheafOfModules PS m) U).hom := by
  dsimp only
  rfl

/-- The inverse chart trivialization is literal multiplication by `X_i^m`
after the ordinary structure-function and degree-zero identifications. -/
lemma p2PositiveTwistSectionsIsoUnit_inv
    (U : Scheme.Opens (Proj PS)) (i : Fin 3)
    (hU : U ≤ p2StandardOpen (K := K) i) (m : ℕ) :
    let F := forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat
    let a := degreeOnePower PS (p2Coordinate K i) m
    let eadd : positiveSheafOfModules PS (0 + m) ≅
        positiveSheafOfModules PS m := eqToIso (by rw [zero_add])
    let f : positiveSheafOfModules PS 0 ⟶ positiveSheafOfModules PS m :=
      positiveMulHomogeneous PS a 0 ≫ eadd.hom
    (p2PositiveTwistSectionsIsoUnit K U i hU m).inv =
      F.map U.topIso.hom ≫
        ((Scheme.Modules.toPresheaf (Proj PS)).map
          (unitToZeroTwist PS)).app (op U) ≫
        ((Scheme.Modules.toPresheaf (Proj PS)).map
          (zeroTwistToPositiveZero PS)).app (op U) ≫
        ((Scheme.Modules.toPresheaf (Proj PS)).map f).app (op U) := by
  dsimp only
  let R := Scheme.Modules.restrictFunctor U.ι
  let a := degreeOnePower PS (p2Coordinate K i) m
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
    have hsx : (degreeOnePower PS (p2Coordinate K i) m : S) ∈
        (positivePointIdeal PS (U.ι x)).primeCompl := by
      change (MvPolynomial.X i : S) ^ m ∈
        (positivePointIdeal PS (U.ι x)).primeCompl
      exact Submonoid.pow_mem _ hXi m
    change IsIso ((TopCat.Presheaf.stalkFunctor _ (U.ι x)).map
      (positiveMulHomogeneousPresheaf PS
        (degreeOnePower PS (p2Coordinate K i) m) 0))
    apply positiveMulHomogeneous_stalkMap_isIso_of_mem_primeCompl_of_irrelevant_le_span
      PS (degreeOnePower PS (p2Coordinate K i) m) 0 (U.ι x) hsx
    exact (p2Coordinates_span_irrelevant K).trans (Ideal.span_mono (by
      rintro _ ⟨j, rfl⟩
      exact ⟨p2Coordinate K j, rfl⟩))
  letI : IsIso (R.map f₀) := hf₀
  letI : IsIso (R.map f) := by
    dsimp only [f]
    rw [R.map_comp]
    infer_instance
  rw [p2PositiveTwistSectionsIsoUnit_inv_decompose K U i hU m]
  let e := p2PositiveTwistOpenIsoUnit K U i hU m
  change ((Scheme.Modules.toPresheaf (U : Scheme)).map e.inv).app (op ⊤) ≫
      (moduleRestrictTopIso (positiveSheafOfModules PS m) U).hom = _
  have heinv : e.inv =
      (((Scheme.Modules.restrictUnitIso U.ι).inv ≫
          R.map (unitIsoZeroTwist PS).hom) ≫
        R.map (positiveZeroTwistIso PS).inv) ≫ R.map f := by
    dsimp only [e, p2PositiveTwistOpenIsoUnit]
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

/-- Pointwise, the inverse of the positive chart trivialization multiplies
the chart function by `X_i^m`. -/
lemma p2PositiveTwistSectionsIsoUnit_inv_apply_val
    (U : Scheme.Opens (Proj PS)) (i : Fin 3)
    (hU : U ≤ p2StandardOpen (K := K) i) (m : ℕ)
    (r : Γ((U : Scheme), ⊤)) (x : U) :
    ((p2PositiveTwistSectionsIsoUnit K U i hU m).inv r).1 x =
      algebraMap S (PositiveFiber PS x.1)
          ((degreeOnePower PS (p2Coordinate K i) m : PS m) : S) *
        ((((forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).map
          U.topIso.hom) r).1 x).val := by
  rw [p2PositiveTwistSectionsIsoUnit_inv K U i hU m]
  let F := forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat
  let q := F.map U.topIso.hom r
  let z₀ := ((Scheme.Modules.toPresheaf (Proj PS)).map
    (unitToZeroTwist PS)).app (op U) q
  let p₀ := ((Scheme.Modules.toPresheaf (Proj PS)).map
    (zeroTwistToPositiveZero PS)).app (op U) z₀
  let zm := (positiveMulHomogeneous PS
    (degreeOnePower PS (p2Coordinate K i) m) 0).val.app (op U) p₀
  let eadd : positiveSheafOfModules PS (0 + m) ≅
      positiveSheafOfModules PS m := eqToIso (by rw [zero_add])
  change (((eadd.hom.val.app (op U)) zm).1 x) = _
  rw [positiveZeroAddCast_apply_val K m (op U) zm x]
  change algebraMap S (PositiveFiber PS x.1)
      ((degreeOnePower PS (p2Coordinate K i) m : PS m) : S) * p₀.1 x = _
  rfl

/-- The positive chart trivialization with its values transported to ambient
structure-sheaf sections on the same open. -/
noncomputable def p2PositiveTwistSectionsIsoStructure
    (U : Scheme.Opens (Proj PS)) (i : Fin 3)
    (hU : U ≤ p2StandardOpen (K := K) i) (m : ℕ) :
    Γ(positiveSheafOfModules PS m, U) ≅
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).obj
        Γ(Proj PS, U) :=
  p2PositiveTwistSectionsIsoUnit K U i hU m ≪≫
    (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).mapIso U.topIso

/-- The single ambient sheaf morphism whose local components are the
inverses of all positive chart trivializations for the coordinate `X_i`. -/
noncomputable def p2PositiveTwistTrivializationInvHom
    (i : Fin 3) (m : ℕ) :
    SheafOfModules.unit (Proj PS).ringCatSheaf ⟶
      positiveSheafOfModules PS m :=
  let a := degreeOnePower PS (p2Coordinate K i) m
  let eadd : positiveSheafOfModules PS (0 + m) ≅
      positiveSheafOfModules PS m := eqToIso (by rw [zero_add])
  unitToZeroTwist PS ≫ zeroTwistToPositiveZero PS ≫
    (positiveMulHomogeneous PS a 0 ≫ eadd.hom)

/-- The inverse positive chart is the component of one ambient sheaf
morphism; in particular it is compatible with every restriction map. -/
lemma p2PositiveTwistSectionsIsoStructure_inv
    (U : Scheme.Opens (Proj PS)) (i : Fin 3)
    (hU : U ≤ p2StandardOpen (K := K) i) (m : ℕ) :
    (p2PositiveTwistSectionsIsoStructure K U i hU m).inv =
      ((Scheme.Modules.toPresheaf (Proj PS)).map
        (p2PositiveTwistTrivializationInvHom K i m)).app (op U) := by
  let F := forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat
  let a := degreeOnePower PS (p2Coordinate K i) m
  let eadd : positiveSheafOfModules PS (0 + m) ≅
      positiveSheafOfModules PS m := eqToIso (by rw [zero_add])
  let f : positiveSheafOfModules PS 0 ⟶ positiveSheafOfModules PS m :=
    positiveMulHomogeneous PS a 0 ≫ eadd.hom
  change F.map U.topIso.inv ≫
      (p2PositiveTwistSectionsIsoUnit K U i hU m).inv = _
  rw [p2PositiveTwistSectionsIsoUnit_inv K U i hU m]
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
  simp

/-- Positive chart trivializations commute with restriction between opens in
the same coordinate chart. -/
lemma p2PositiveTwistSectionsIsoStructure_natural
    (U V : Scheme.Opens (Proj PS)) (hVU : V ≤ U) (i : Fin 3)
    (hU : U ≤ p2StandardOpen (K := K) i) (m : ℕ) :
    (positiveSheafOfModules PS m).presheaf.map (homOfLE hVU).op ≫
        (p2PositiveTwistSectionsIsoStructure K V i (hVU.trans hU) m).hom =
      (p2PositiveTwistSectionsIsoStructure K U i hU m).hom ≫
        (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).map
          ((Proj PS).presheaf.map (homOfLE hVU).op) := by
  let eU := p2PositiveTwistSectionsIsoStructure K U i hU m
  let eV := p2PositiveTwistSectionsIsoStructure K V i (hVU.trans hU) m
  let rP := (positiveSheafOfModules PS m).presheaf.map (homOfLE hVU).op
  let rO := (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).map
    ((Proj PS).presheaf.map (homOfLE hVU).op)
  have hinv : rO ≫ eV.inv = eU.inv ≫ rP := by
    rw [p2PositiveTwistSectionsIsoStructure_inv K,
      p2PositiveTwistSectionsIsoStructure_inv K]
    exact ((Scheme.Modules.toPresheaf (Proj PS)).map
      (p2PositiveTwistTrivializationInvHom K i m)).naturality (homOfLE hVU).op
  apply (cancel_mono eV.inv).mp
  change (rP ≫ eV.hom) ≫ eV.inv = (eU.hom ≫ rO) ≫ eV.inv
  simp only [Category.assoc, eV.hom_inv_id, Category.comp_id]
  rw [hinv]
  simp

/-- On a homogeneous basic open contained in `D₊(X_i)`, positive-twist
sections are degree-zero homogeneous localizations after division by the
chart basis `X_i^m`. -/
noncomputable def p2PositiveTwistBasicOpenIsoAway
    (f : S) (d : ℕ) (hf : f ∈ PS d) (hd : 0 < d)
    (i : Fin 3) (hdiv : MvPolynomial.X i ∣ f) (m : ℕ) :
    Γ(positiveSheafOfModules PS m,
        AlgebraicGeometry.Proj.basicOpen PS f) ≅
      AddCommGrpCat.of (HomogeneousLocalization.Away PS f) := by
  let U := AlgebraicGeometry.Proj.basicOpen PS f
  have hU : U ≤ p2StandardOpen (K := K) i :=
    AlgebraicGeometry.Proj.basicOpen_mono PS
      (MvPolynomial.X i) f hdiv
  let F := forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat
  exact p2PositiveTwistSectionsIsoUnit K U i hU m ≪≫
    F.mapIso U.topIso ≪≫
    F.mapIso (AlgebraicGeometry.Proj.basicOpenIsoAway PS f hf hd).symm

lemma p2PositiveTwistBasicOpenIsoAway_hom
    (f : S) (d : ℕ) (hf : f ∈ PS d) (hd : 0 < d)
    (i : Fin 3) (hdiv : MvPolynomial.X i ∣ f) (m : ℕ) :
    let U := AlgebraicGeometry.Proj.basicOpen PS f
    let hU : U ≤ p2StandardOpen (K := K) i :=
      AlgebraicGeometry.Proj.basicOpen_mono PS (MvPolynomial.X i) f hdiv
    let F := forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat
    (p2PositiveTwistBasicOpenIsoAway K f d hf hd i hdiv m).hom =
      (p2PositiveTwistSectionsIsoStructure K U i hU m).hom ≫
        F.map (AlgebraicGeometry.Proj.basicOpenIsoAway PS f hf hd).inv := by
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Restriction from `D₊(f)` to `D₊(fg)` is carried by the positive chart
coordinates to the canonical map of homogeneous localizations. -/
theorem positiveTwistBasicOpenIsoAway_natural
    (f g x : S) (d e : ℕ)
    (hf : f ∈ PS d) (hg : g ∈ PS e) (hd : 0 < d)
    (hx : x = f * g) (i : Fin 3) (hdiv : MvPolynomial.X i ∣ f) (m : ℕ) :
    (positiveSheafOfModules PS m).presheaf.map
        (homOfLE (AlgebraicGeometry.Proj.basicOpen_mono PS f x ⟨g, hx⟩)).op ≫
      (p2PositiveTwistBasicOpenIsoAway K x (d + e)
        (hx ▸ SetLike.mul_mem_graded hf hg) (Nat.add_pos_left hd e) i
        (dvd_trans hdiv ⟨g, hx⟩) m).hom =
    (p2PositiveTwistBasicOpenIsoAway K f d hf hd i hdiv m).hom ≫
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).map
        (CommRingCat.ofHom (HomogeneousLocalization.awayMap PS hg hx)) := by
  let Uf := AlgebraicGeometry.Proj.basicOpen PS f
  let Ux := AlgebraicGeometry.Proj.basicOpen PS x
  let hxf : Ux ≤ Uf :=
    AlgebraicGeometry.Proj.basicOpen_mono PS f x ⟨g, hx⟩
  let hfi : Uf ≤ p2StandardOpen (K := K) i :=
    AlgebraicGeometry.Proj.basicOpen_mono PS (MvPolynomial.X i) f hdiv
  let hxi : Ux ≤ p2StandardOpen (K := K) i := hxf.trans hfi
  let F := forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat
  let bx := F.map (AlgebraicGeometry.Proj.basicOpenIsoAway PS x
    (hx ▸ SetLike.mul_mem_graded hf hg) (Nat.add_pos_left hd e)).inv
  let bf := F.map
    (AlgebraicGeometry.Proj.basicOpenIsoAway PS f hf hd).inv
  let amap := F.map
    (CommRingCat.ofHom (HomogeneousLocalization.awayMap PS hg hx))
  rw [p2PositiveTwistBasicOpenIsoAway_hom K,
    p2PositiveTwistBasicOpenIsoAway_hom K]
  have htwist := p2PositiveTwistSectionsIsoStructure_natural
    K Uf Ux hxf i hfi m
  have haway := basicOpenIsoAway_inv_natural_addCommGrp
    K f g x d e hf hg hd hx
  change (positiveSheafOfModules PS m).presheaf.map (homOfLE hxf).op ≫
      (p2PositiveTwistSectionsIsoStructure K Ux i hxi m).hom ≫ bx =
    (p2PositiveTwistSectionsIsoStructure K Uf i hfi m).hom ≫ bf ≫ amap
  rw [← Category.assoc, htwist]
  simp only [Category.assoc]
  rw [haway]

/-- Sections of the positive twist on a standard coordinate chart are
identified with sections of the structure sheaf on that chart.  Concretely,
the trivialization divides a degree-`m` section by `X_i^m`. -/
noncomputable def p2PositiveTwistStandardOpenSectionsIsoUnit
    (i : Fin 3) (m : ℕ) (hm : 0 < m) :
    Γ(positiveSheafOfModules PS m, p2StandardOpen (K := K) i) ≅
      AddCommGrpCat.of Γ((p2StandardOpen (K := K) i : Scheme), ⊤) := by
  exact p2PositiveTwistSectionsIsoUnit K
    (p2StandardOpen (K := K) i) i le_rfl m

/-- On `D₊(X_i)`, sections of `O(m)` are degree-zero elements of the
homogeneous localization at `X_i`; the `O(m)` grading is accounted for by
the chart basis `X_i^m`. -/
noncomputable def p2PositiveTwistStandardOpenIsoAway
    (i : Fin 3) (m : ℕ) (hm : 0 < m) :
    Γ(positiveSheafOfModules PS m, p2StandardOpen (K := K) i) ≅
      AddCommGrpCat.of (HomogeneousLocalization.Away PS (MvPolynomial.X i)) := by
  let U := p2StandardOpen (K := K) i
  exact p2PositiveTwistBasicOpenIsoAway K (MvPolynomial.X i) 1
    (MvPolynomial.isHomogeneous_X K i) (by decide) i (dvd_refl _) m

end PfaffianDescent.ProjectivePlaneNative
