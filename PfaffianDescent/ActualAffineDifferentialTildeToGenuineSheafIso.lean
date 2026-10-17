import PfaffianDescent.ActualAffineDifferentialTildeToGenuineSheaf
import PfaffianDescent.ActualAffineDifferentialPresheafSheafIso
import PfaffianDescent.ActualBundledKaehlerRingIsoMap

/- SOURCE ONLY / UNVERIFIED. The original 193/195 maps are unchanged.
The true top coefficient square, native algebra transport and genuine
sheafification unit are used once. No QC/Iso comparison input. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]

private lemma actualAffineTopDifferentialScalarSquare_forIso :
    (𝟙 (CommRingCat.of k)) ≫
      (schemeBaseScalarPresheafMap
        (Spec.map (CommRingCat.ofHom (algebraMap k R)))).app (op ⊤) =
      CommRingCat.ofHom (algebraMap k R) ≫ (Scheme.ΓSpecIso (.of R)).inv := by
  let X := Spec (CommRingCat.of R)
  have hres : X.presheaf.map
      (homOfLE (show (⊤ : X.Opens) ≤ ⊤ from le_top)).op = 𝟙 _ := by
    rw [show (homOfLE (show (⊤ : X.Opens) ≤ ⊤ from le_top)).op =
      𝟙 (op (⊤ : X.Opens)) from Subsingleton.elim _ _, CategoryTheory.Functor.map_id]
  change (𝟙 (CommRingCat.of k)) ≫
    ((Scheme.ΓSpecIso (.of k)).inv ≫
      (Spec.map (CommRingCat.ofHom (algebraMap k R))).appTop ≫
        X.presheaf.map (homOfLE (show (⊤ : X.Opens) ≤ ⊤ from le_top)).op) = _
  rw [Category.id_comp, hres, Category.comp_id]
  exact (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (algebraMap k R))).symm

/-- Composition of actual module morphisms, with its factors kept explicit. -/
private lemma actualModuleCatComposite_bijective
    {S : Type u} [CommRing S] {M N P : ModuleCat S}
    (a : M ⟶ N) (b : N ⟶ P)
    (ha : Function.Bijective a) (hb : Function.Bijective b) :
    Function.Bijective (a ≫ b).hom := hb.comp ha

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The EXISTING genuine top differential map is bijective. Its native
algebra EqToIso is the same one already internally constructed in193. -/
lemma actualAffineDifferentialTopToGenuineSheaf_bijective :
    Function.Bijective (actualAffineDifferentialTopToGenuineSheaf
      (k := k) (R := R)) := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap k R))
  let c := (Scheme.ΓSpecIso (CommRingCat.of R)).inv
  let sigma := schemeBaseScalarPresheafMap g
  have hb : Function.Bijective (CommRingCat.KaehlerDifferential.map
      (actualAffineTopDifferentialScalarSquare_forIso (k := k) (R := R))) :=
    actualBundledKaehlerRingIsoMap_bijective (algebraMap k R)
      (sigma.app (op ⊤)).hom
      ((Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv)
      (actualAffineTopDifferentialScalarSquare_forIso (k := k) (R := R))
  have hu := actualAffineDifferentialPresheafUnit_top_bijective
    (k := k) (R := R)
  let O := schemeRelativeDifferentials g
  let eta := (PresheafOfModules.sheafificationAdjunction
    (𝟙 (Spec (CommRingCat.of R)).ringCatSheaf.obj)).unit.app
      (schemeRelativeDifferentialsPresheaf g)
  let v : CommRingCat.KaehlerDifferential
      (CommRingCat.ofHom (algebraMap k R)) ⟶
      (moduleSpecΓFunctor (R := CommRingCat.of R)).obj O :=
    CommRingCat.KaehlerDifferential.map
      (actualAffineTopDifferentialScalarSquare_forIso (k := k) (R := R)) ≫
        (ModuleCat.restrictScalars c.hom).map (eta.app (op ⊤))
  have hv : Function.Bijective v := hu.comp hb
  unfold actualAffineDifferentialTopToGenuineSheaf
  dsimp only
  exact actualModuleCatComposite_bijective _ v
    (ConcreteCategory.bijective_of_isIso _) hv

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The EXISTING tilde-adjoint195 is an Iso. The target's genuine
localizing property and the actual top map bijection are derived above. -/
lemma actualAffineDifferentialTildeToGenuineSheaf_isIso :
    IsIso (actualAffineDifferentialTildeToGenuineSheaf (k := k) (R := R)) := by
  let M := ModuleCat.of R (KaehlerDifferential k R)
  let O := schemeRelativeDifferentials
    (Spec.map (CommRingCat.ofHom (algebraMap k R)))
  let A := actualAffineDifferentialTildeToGenuineSheaf (k := k) (R := R)
  let G := moduleSpecΓFunctor (R := CommRingCat.of R)
  let u := ((tilde.toTildeΓNatIso (R := CommRingCat.of R)).app M).hom
  let v : M ⟶ G.obj O := ModuleCat.ofHom
    (X := M) (Y := G.obj O)
    (actualAffineDifferentialTopToGenuineSheaf (k := k) (R := R))
  have hv : IsIso v :=
    (ConcreteCategory.isIso_iff_bijective v).mpr
      (actualAffineDifferentialTopToGenuineSheaf_bijective (k := k) (R := R))
  have he : u ≫ G.map A = v := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact actualAffineDifferentialTildeToGenuineSheaf_unit (k := k) (R := R) x
  letI : IsIso (u ≫ G.map A) := he.symm ▸ hv
  have hTop : IsIso (G.map A) := IsIso.of_isIso_comp_left u (G.map A)
  have hSource := isLocalizing_tilde (R := CommRingCat.of R) M
  have hTarget := actualAffineGenuineDifferentialSheaf_localizing
    (k := k) (R := R)
  letI : IsIso ((modulesSpecToSheaf (R := CommRingCat.of R)).map A) :=
    isLocalizing_of_isIso_app_top hTop hSource hTarget
  exact (SpecModulesToSheafFullyFaithful (R := CommRingCat.of R)).isIso_of_isIso_map A

end PfaffianDescent
