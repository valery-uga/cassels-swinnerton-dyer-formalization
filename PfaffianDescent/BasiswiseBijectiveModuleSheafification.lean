import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Topology.Sheaves.SheafCondition.Sites
import Mathlib.CategoryTheory.Sites.LocallyBijective

/- SOURCE ONLY / UNVERIFIED. Generic auxiliary: bijectivity on a genuine
basis gives a sheafification Iso. The actual Kähler caller derives basis
bijectivity from its internally constructed canonical equivalences. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
universe u
variable {X : Scheme.{u}} {ι : Type u}

lemma modulePresheaf_basiswise_locallyBijective
    {P Q : X.PresheafOfModules} (a : P ⟶ Q)
    (B : ι → X.Opens) (hB : Opens.IsBasis (Set.range B))
    (ha : ∀ i, Function.Bijective (a.app (op (B i)))) :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf _).map a) ∧
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf _).map a) := by
  constructor
  · refine ⟨?_⟩
    intro U x y hxy
    intro z hz
    obtain ⟨V, ⟨i, rfl⟩, hzV, hVU⟩ := (Opens.isBasis_iff_nbhd.mp hB) hz
    refine ⟨B i, homOfLE hVU, ?_, hzV⟩
    change P.map (homOfLE hVU).op x = P.map (homOfLE hVU).op y
    apply (ha i).injective
    have hxy' : a.app U x = a.app U y := hxy
    exact (PresheafOfModules.naturality_apply a (homOfLE hVU).op x).trans
      ((congrArg (fun t => Q.map (homOfLE hVU).op t) hxy').trans
        (PresheafOfModules.naturality_apply a (homOfLE hVU).op y).symm)
  · refine ⟨?_⟩
    intro U s
    intro z hz
    obtain ⟨V, ⟨i, rfl⟩, hzV, hVU⟩ := (Opens.isBasis_iff_nbhd.mp hB) hz
    refine ⟨B i, homOfLE hVU, ?_, hzV⟩
    exact (ha i).surjective (Q.map (homOfLE hVU).op s)

lemma moduleSheafification_map_isIso_of_basiswise_bijective
    {P Q : X.PresheafOfModules} (a : P ⟶ Q)
    (B : ι → X.Opens) (hB : Opens.IsBasis (Set.range B))
    (ha : ∀ i, Function.Bijective (a.app (op (B i)))) :
    IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map a) := by
  let J := Opens.grothendieckTopology X
  let b := (PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map a
  obtain ⟨hi, hs⟩ := modulePresheaf_basiswise_locallyBijective a B hB ha
  letI := hi
  letI := hs
  have hi' : Sheaf.IsLocallyInjective ((presheafToSheaf J AddCommGrpCat).map b) :=
    (Presheaf.isLocallyInjective_presheafToSheaf_map_iff J b).mpr hi
  have hs' : Sheaf.IsLocallySurjective ((presheafToSheaf J AddCommGrpCat).map b) :=
    (Presheaf.isLocallySurjective_presheafToSheaf_map_iff J b).mpr hs
  haveI : IsIso ((presheafToSheaf J AddCommGrpCat).map b) :=
    (Sheaf.isLocallyBijective_iff_isIso _).mp ⟨hi', hs'⟩
  haveI : IsIso ((SheafOfModules.toSheaf X.ringCatSheaf).map
      ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map a)) := by
    change IsIso ((presheafToSheaf J AddCommGrpCat).map b)
    infer_instance
  exact isIso_of_reflects_iso _ (SheafOfModules.toSheaf X.ringCatSheaf)

end PfaffianDescent
