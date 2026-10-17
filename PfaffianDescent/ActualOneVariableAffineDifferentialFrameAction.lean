import PfaffianDescent.ActualOneVariableAffineDifferentialFrame

/- SOURCE ONLY / UNVERIFIED. Named universal D(t) action of the GENUINE
polynomial affine Omega frame; all original scalar/top section maps retained. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u v w
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Compute an Iso chain under a module-valued functor while all objects,
Isos and point values are abstract, before inserting actual Omega objects. -/
private theorem moduleValuedFunctor_isoChain_apply
    {R : Type u} [CommRing R] {C : Type v} [Category.{w} C]
    (G : C ⥤ ModuleCat R) {A B D E : C}
    (a : A ≅ B) (b : B ≅ D) (c : D ≅ E) (x : G.obj A) :
    G.map (a ≪≫ b ≪≫ c).hom x =
      G.map c.hom (G.map b.hom (G.map a.hom x)) := by
  simp only [Iso.trans_hom, Functor.map_comp, ModuleCat.comp_apply]

/-- Naturality of the ORIGINAL native tilde/global-sections unit. -/
private theorem affineTildeNativeUnit_naturality
    {R : Type u} [CommRing R] {M N : ModuleCat R} (f : M ⟶ N) (x : M) :
    (moduleSpecΓFunctor (R := .of R)).map
      ((tilde.functor (.of R)).map f)
        (((tilde.toTildeΓNatIso (R := .of R)).app M).hom x) =
      ((tilde.toTildeΓNatIso (R := .of R)).app N).hom (f x) := by
  exact (ConcreteCategory.congr_hom
    ((tilde.toTildeΓNatIso (R := .of R)).hom.naturality f) x).symm

/-- The native tildeSelf frame sends the ORIGINAL native unit class to
the ORIGINAL structure-sheaf top section, not a transported scalar. -/
private theorem affineTildeSelf_nativeUnit
    {R : Type u} [CommRing R] (r : R) :
    (moduleSpecΓFunctor (R := .of R)).map (tildeSelf (R := .of R)).hom
      (((tilde.toTildeΓNatIso (R := .of R)).app (ModuleCat.of R R)).hom r) =
      (affineGlobalSectionsUnitLinearEquiv (A := R)).symm r := by
  change (moduleSpecΓFunctor (R := .of R)).map
    (𝟙 ((tilde.functor (.of R)).obj (ModuleCat.of R R)))
      (((tilde.toTildeΓNatIso (R := .of R)).app (ModuleCat.of R R)).hom r) = _
  rw [CategoryTheory.Functor.map_id, ModuleCat.id_apply]
  exact (ConcreteCategory.congr_hom
    (affineGlobalSectionsUnitLinearEquiv_symm_eq_tildeAdjunctionUnit (A := R)) r).symm

/-- Genuine coefficient action for an actual tilde frame. The only generic
point hypothesis is its explicit native top action; the D(t) caller derives it. -/
private theorem genuineAffineTildeFrameChain_nativeTop
    {R : Type u} [CommRing R] {Q : (Spec (.of R)).Modules} {M : ModuleCat R}
    (e : Q ≅ (tilde.functor (.of R)).obj M)
    (l : M ≅ ModuleCat.of R R)
    (z : (moduleSpecΓFunctor (R := .of R)).obj Q) (x : M)
    (he : (moduleSpecΓFunctor (R := .of R)).map e.hom z =
      ((tilde.toTildeΓNatIso (R := .of R)).app M).hom x) :
    (moduleSpecΓFunctor (R := .of R)).map
      (e ≪≫ (tilde.functor (.of R)).mapIso l ≪≫ (tildeSelf (R := .of R))).hom z =
      (affineGlobalSectionsUnitLinearEquiv (A := R)).symm (l.hom x) := by
  let G := moduleSpecΓFunctor (R := .of R)
  calc
    _ = G.map (tildeSelf (R := .of R)).hom
        (G.map ((tilde.functor (.of R)).map l.hom) (G.map e.hom z)) :=
      moduleValuedFunctor_isoChain_apply G e ((tilde.functor (.of R)).mapIso l)
        (tildeSelf (R := .of R)) z
    _ = G.map (tildeSelf (R := .of R)).hom
        (((tilde.toTildeΓNatIso (R := .of R)).app (ModuleCat.of R R)).hom (l.hom x)) := by
      rw [he, affineTildeNativeUnit_naturality]
    _ = _ := affineTildeSelf_nativeUnit (l.hom x)

/-- The GENUINE affine differential frame sends the ACTUAL sheafified
universal D(X_a) section to1 in the ORIGINAL coefficient trivialization. -/
theorem actualOneVariableAffineDifferentialFrameIso_D
    {K : Type u} [CommRing K] {σ : Type} [Subsingleton σ] (a : σ) :
    (moduleSpecΓFunctor (R := .of (MvPolynomial σ K))).map
      (actualOneVariableAffineDifferentialFrameIso (K := K) a).hom
      (actualRelativeDifferentialSection
        (Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial σ K)))) ⊤
        ((Scheme.ΓSpecIso (.of (MvPolynomial σ K))).inv.hom (MvPolynomial.X a))) =
      (affineGlobalSectionsUnitLinearEquiv (A := MvPolynomial σ K)).symm 1 := by
  let R := MvPolynomial σ K
  let d := KaehlerDifferential.D K R (MvPolynomial.X a)
  let e := actualAffineDifferentialGenuineToTildeIso (k := K) (R := R)
  let l := (oneVariablePolynomialKaehlerFrame (K := K) a).toModuleIso
  have he := actualAffineDifferentialGenuineToTildeIso_nativeTop (k := K) (R := R) d
  rw [actualAffineDifferentialTopToGenuineSheaf_D] at he
  have h := genuineAffineTildeFrameChain_nativeTop e l _ d he
  change (moduleSpecΓFunctor (R := .of R)).map
    (e ≪≫ (tilde.functor (.of R)).mapIso l ≪≫ tildeSelf).hom _ = _
  have hl : l.hom d = (1 : R) := oneVariablePolynomialKaehlerFrame_D (K := K) a
  rw [hl] at h
  exact h

end PfaffianDescent
end
