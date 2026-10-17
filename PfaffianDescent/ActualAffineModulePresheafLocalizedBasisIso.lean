import PfaffianDescent.ActualAffineModulePresheafTopRestrictionNatural
import PfaffianDescent.ActualLocalizedFunctorComparison

/- SOURCE ONLY / UNVERIFIED. Generic P basis Iso. Target denominator
units are derived from its real tilde sheaf and actual open inclusions.
No graph, QC, sheaf comparison, derivative or unit certificate input. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite
universe u v w

/-- Constant-source whiskering with its source written as the actual
constant functor on C. This is constructed before any actual Ptop module
is substituted; its components are exactly ordinary left whiskering. -/
private def actualWhiskerLeftConstantModule
    {R : Type u} [CommRing R] {C : Type v} {D : Type w}
    [Category C] [Category D] (H : C ⥤ D) {M : ModuleCat R}
    {G : D ⥤ ModuleCat R} (a : (Functor.const D).obj M ⟶ G) :
    (Functor.const C).obj M ⟶ H ⋙ G where
  app c := a.app (H.obj c)
  naturality c d i := a.naturality (H.map i)

/-- If a divides a power of the localized element b, its scalar action
is a unit on the SAME actual target module of the localization map. -/
private lemma actualLocalizedModule_divisorDenominatorUnits
    {R : Type u} [CommRing R] {M N : ModuleCat R}
    (v : M →ₗ[R] N) (a b : R)
    [IsLocalizedModule (Submonoid.powers b) v]
    (hdiv : ∃ n : ℕ, a ∣ b ^ n) (s : Submonoid.powers a) :
    IsUnit (algebraMap R (Module.End R N) s) := by
  have hb := IsLocalizedModule.map_units v
    ⟨b, Submonoid.mem_powers b⟩
  obtain ⟨n, t, ht⟩ := hdiv
  have hprod : IsUnit
      (algebraMap R (Module.End R N) a *
        algebraMap R (Module.End R N) t) := by
    simpa only [← map_pow, ht, map_mul] using hb.pow n
  have ha := (((Commute.all a t).map
    (algebraMap R (Module.End R N))).isUnit_mul_iff.mp hprod).1
  obtain ⟨m, hm⟩ := (Submonoid.mem_powers_iff (s : R) a).mp s.property
  simpa only [← map_pow, hm] using ha.pow m

set_option backward.isDefEq.respectTransparency false in
noncomputable def actualAffineModulePresheafLocalizedBasisIso
    {R : Type u} [CommRing R]
    (P : (Spec (CommRingCat.of R)).PresheafOfModules)
    (hLoc : ∀ f : R, IsLocalizedModule (Submonoid.powers f)
      (((actualAffineModulePresheafOverBase P).map
        (PrimeSpectrum.basicOpen f).leTop.op).hom)) :=
  let X := Spec (CommRingCat.of R)
  let B : R → X.Opens := PrimeSpectrum.basicOpen
  let H := (inducedFunctor B).op
  let F₀ := actualAffineModulePresheafOverBase P
  let M := F₀.obj (op ⊤)
  let N := tilde (R := CommRingCat.of R) M
  let G₀ := ((modulesSpecToSheaf (R := CommRingCat.of R)).obj N).obj
  let F := H ⋙ F₀
  let G := H ⋙ G₀
  let f : (Functor.const (InducedCategory X.Opens B)ᵒᵖ).obj M ⟶ F :=
    Functor.whiskerLeft H (actualAffineModulePresheafTopRestriction P)
  let g := actualWhiskerLeftConstantModule (R := R) H
    (actualAffineModulePresheafTopToTilde P)
  let S : (InducedCategory X.Opens B)ᵒᵖ → Submonoid R :=
    fun c => Submonoid.powers (c.unop : R)
  have hf : ∀ c, IsLocalizedModule (S c) (f.app c).hom :=
    fun c => hLoc (c.unop : R)
  have hg : ∀ c, IsLocalizedModule (S c) (g.app c).hom :=
    fun c => tilde.instAwayCarrierCarrierObjOppositeOpensCarrierCarrierCommRingCatSpecModuleCatPresheafModulesSheafModulesSpecToSheafOpBasicOpenHomToOpen (R := CommRingCat.of R) M (c.unop : R)
  have hu : ∀ (c d : (InducedCategory X.Opens B)ᵒᵖ) (i : c ⟶ d) (s : S c),
      IsUnit (algebraMap R (Module.End R (G.obj d)) s) := by
    intro c d i s
    let a : R := c.unop
    let b : R := d.unop
    letI : IsLocalizedModule (R := R)
        (Submonoid.powers (M := R) b) (g.app d).hom := hg d
    have hle : PrimeSpectrum.basicOpen (R := R) b ≤
        PrimeSpectrum.basicOpen (R := R) a :=
      leOfHom ((inducedFunctor B).map i.unop)
    have hdiv : ∃ n : ℕ, a ∣ b ^ n := by
      simpa only [Ideal.mem_radical_iff, Ideal.mem_span_singleton] using
        (PrimeSpectrum.basicOpen_le_basicOpen_iff (R := R) b a).mp hle
    exact actualLocalizedModule_divisorDenominatorUnits (R := R)
      (g.app d).hom a b hdiv s
  actualLocalizedFunctorComparison (R := R)
    (C := (InducedCategory X.Opens B)ᵒᵖ) M F _ f g S hf hg hu

end PfaffianDescent
