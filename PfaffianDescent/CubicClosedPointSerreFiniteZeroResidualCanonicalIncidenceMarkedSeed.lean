import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualSeedMarkedOpen
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualFibreFiniteEtaleIso
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualIncidenceMarkedOpen
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceCanonicalSeedLift
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceSeedFibreProjection

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_canonicalSupport_exists_marked_seed
    {K E : Type u} [Field K] [Field E] [Algebra K E] [FiniteDimensional K E]
    {B X P Z D : Scheme.{u}}
    (b : B ⟶ Spec (.of K)) [LocallyOfFiniteType b] [IsSeparated b]
    (x : X ⟶ Spec (.of K)) [IsProper x]
    (p : P ⟶ Spec (.of K)) [LocallyOfFiniteType p] [IsSeparated p]
    (marked : Fin 3 → (B ⟶ X)) (hm : ∀ n, marked n ≫ x = b)
    (zero : Z ⟶ pullback x p) [IsClosedImmersion zero]
    (t : Spec (.of K) ⟶ P) (ht : t ≫ p = 𝟙 _)
    (d : D ⟶ Spec (.of K)) [IsFinite d] [Etale d] (i : D ⟶ X)
    (v : D ≅ pullback (zero ≫ pullback.snd x p) t)
    (hv : v.hom ≫ pullback.snd (zero ≫ pullback.snd x p) t = d)
    (hvs : v.hom ≫ pullback.fst (zero ≫ pullback.snd x p) t ≫ zero ≫ pullback.fst x p = i)
    (c : Spec (.of E) ⟶ B)
    (hc : c ≫ b = Spec.map (CommRingCat.ofHom (algebraMap K E)))
    (δ : Fin 3 → (Spec (.of E) ⟶ D))
    (hδd : ∀ n, δ n ≫ d = Spec.map (CommRingCat.ofHom (algebraMap K E)))
    (hδi : ∀ n, δ n ≫ i = c ≫ marked n) :
    ∃ s : Spec (.of E) ⟶ serreThreePointSectionIncidence b x p marked hm zero,
      s ≫ serreThreePointSectionIncidenceToParameters b x p marked hm zero =
        Spec.map (CommRingCat.ofHom (algebraMap K E)) ≫ t ∧
      s ≫ serreThreePointSectionIncidenceToConfiguration b x p marked hm zero = c ∧
      s (IsLocalRing.closedPoint E) ∈
        cubicClosedPointSerreFiniteZeroResidual_incidenceMarkedOpen b x p marked hm zero ∧
      IsFinite (pullback.snd (serreThreePointSectionIncidenceZeroFamily b x p marked hm zero) s) ∧
      Etale (pullback.snd (serreThreePointSectionIncidenceZeroFamily b x p marked hm zero) s) := by
  let r := Spec.map (CommRingCat.ofHom (algebraMap K E))
  let a : Spec (.of E) ⟶ pullback b p :=
    pullback.lift c (r ≫ t) (by simp only [Category.assoc, ht, Category.comp_id]; exact hc)
  have ha : a ≫ pullback.snd b p = r ≫ t := pullback.lift_snd _ _ _
  have hds : ∀ n, δ n ≫ i = a ≫ pullback.fst b p ≫ marked n := by
    intro n
    rw [← Category.assoc, pullback.lift_fst]
    exact hδi n
  obtain ⟨s, hsP, hsB⟩ := serreIncidenceCanonicalSupport_exists_seed b x p marked hm zero
    t d i v hv hvs a r ha δ hδd hds
  have hsC : s ≫ serreThreePointSectionIncidenceToConfiguration b x p marked hm zero = c := by
    simpa only [a, pullback.lift_fst] using hsB
  let g := serreThreePointSectionIncidenceZeroFamily b x p marked hm zero
  let f := serreThreePointSectionIncidenceToParameters b x p marked hm zero ≫ p
  letI : IsSeparated f := by dsimp [f]; infer_instance
  letI : LocallyOfFiniteType f := by dsimp [f]; infer_instance
  letI : IsLocallyNoetherian (serreThreePointSectionIncidence b x p marked hm zero) :=
    LocallyOfFiniteType.isLocallyNoetherian f
  letI : IsProper (zero ≫ pullback.snd x p) := inferInstance
  letI : IsProper g := inferInstance
  letI : IsLocallyNoetherian (pullback (zero ≫ pullback.snd x p)
      (serreThreePointSectionIncidenceToParameters b x p marked hm zero) : Scheme) :=
    LocallyOfFiniteType.isLocallyNoetherian g
  let e := serreIncidenceSeedCanonicalFibreIso b x p marked hm zero s t d v hv r hsP
  have he : e.hom ≫ pullback.snd g s = pullback.snd d r :=
    serreIncidenceSeedCanonicalFibreIso_hom_snd b x p marked hm zero s t d v hv r hsP
  have hprops := cubicClosedPointSerreFiniteZeroResidual_fibre_finite_etale_of_iso
    g s (pullback.snd d r) e he
  letI : IsFinite (pullback.snd g s) := hprops.1
  letI : Etale (pullback.snd g s) := hprops.2
  have hsF : s ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K E)) := by
    change s ≫ (serreThreePointSectionIncidenceToParameters b x p marked hm zero ≫ p) = r
    rw [← Category.assoc, hsP, Category.assoc, ht, Category.comp_id]
  have hW := cubicClosedPointSerreFiniteZeroResidual_seed_threeMarkedOpen f g
    (serreIncidenceMarkedZeroSection b x p marked hm zero)
    (serreIncidenceMarkedZeroSection_toIncidence b x p marked hm zero) s hsF
  exact ⟨s, hsP, hsC, hW, hprops.1, hprops.2⟩

end PfaffianDescent
