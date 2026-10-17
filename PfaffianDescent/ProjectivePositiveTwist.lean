import PfaffianDescent.ProjectiveNegativeTwistStalk
import PfaffianDescent.SchemeModuleTensor

/-!
# Positive projective twists

This file constructs the positive counterpart to the concrete negative twists
on `Proj`.  Its local fractions have numerator degree `m` greater than their
denominator degree, so that they pair with the negative twist of the same
degree.
-/

noncomputable section

namespace PfaffianDescent

open scoped DirectSum Pointwise
open DirectSum SetLike Localization
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace

universe u

variable {A σ : Type u} [CommRing A] [SetLike σ A]
  [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

namespace ProjectiveNegativeTwist

section PositiveSheaf

local notation "X" => ProjectiveSpectrum.top 𝒜

/-- The underlying prime ideal of a point of `Proj A`. -/
abbrev positivePointIdeal (x : X) : Ideal A :=
  HomogeneousIdeal.toIdeal (ProjectiveSpectrum.asHomogeneousIdeal x)

instance positivePointIdealIsPrime (x : X) : (positivePointIdeal 𝒜 x).IsPrime :=
  ProjectiveSpectrum.isPrime x

/-- The ambient localization in which a positive-twist stalk is realized. -/
abbrev PositiveFiber (x : X) : Type u :=
  Localization (positivePointIdeal 𝒜 x).primeCompl

/-- A fixed positive homogeneous fraction on an open of `Proj A`. -/
def IsPositiveSectionFraction (m : ℕ) {U : Opens X}
    (f : ∀ x : U, PositiveFiber 𝒜 x.1) : Prop :=
  f = 0 ∨ ∃ (i : ℕ) (a : 𝒜 (m + i)) (b : 𝒜 i)
    (hb : ∀ x : U, (b : A) ∈
      (positivePointIdeal 𝒜 x.1).primeCompl),
      ∀ x : U, f x = Localization.mk (a : A) ⟨(b : A), hb x⟩

/-- Equality of two fixed positive fractions spreads to a neighborhood. -/
theorem isPositiveSectionFraction_eq_neighborhood (m : ℕ)
    {U V : Opens X} {f : ∀ y : U, PositiveFiber 𝒜 y.1}
    {g : ∀ y : V, PositiveFiber 𝒜 y.1}
    (hf : IsPositiveSectionFraction 𝒜 m f)
    (hg : IsPositiveSectionFraction 𝒜 m g)
    (x : X) (hxU : x ∈ U) (hxV : x ∈ V)
    (hx : f ⟨x, hxU⟩ = g ⟨x, hxV⟩) :
    ∃ (W : Opens X) (hxW : x ∈ W) (iWU : W ⟶ U) (iWV : W ⟶ V),
      ∀ w : W, f (iWU w) = g (iWV w) := by
  obtain ⟨a, b, hb, hfval⟩ :
      ∃ (a b : A)
        (hb : ∀ y : U, b ∈ (positivePointIdeal 𝒜 y.1).primeCompl),
        ∀ y : U, f y = Localization.mk a ⟨b, hb y⟩ := by
    rcases hf with rfl | ⟨i, a, b, hb, hval⟩
    · exact ⟨0, 1, fun _ ↦ Submonoid.one_mem _,
        fun _ ↦ (Localization.mk_zero _).symm⟩
    · exact ⟨a, b, hb, hval⟩
  obtain ⟨c, d, hd, hgval⟩ :
      ∃ (c d : A)
        (hd : ∀ y : V, d ∈ (positivePointIdeal 𝒜 y.1).primeCompl),
        ∀ y : V, g y = Localization.mk c ⟨d, hd y⟩ := by
    rcases hg with rfl | ⟨i, c, d, hd, hval⟩
    · exact ⟨0, 1, fun _ ↦ Submonoid.one_mem _,
        fun _ ↦ (Localization.mk_zero _).symm⟩
    · exact ⟨c, d, hd, hval⟩
  rw [hfval, hgval] at hx
  obtain ⟨e, he⟩ := localization_eq_on_basicOpen
    (positivePointIdeal 𝒜 x) (hb ⟨x, hxU⟩) (hd ⟨x, hxV⟩) hx
  let B := ProjectiveSpectrum.basicOpen 𝒜 (e : A)
  let W := (U ⊓ V) ⊓ B
  have hxB : x ∈ B := by
    change (e : A) ∉ x.asHomogeneousIdeal
    exact e.2
  have hxW : x ∈ W := ⟨⟨hxU, hxV⟩, hxB⟩
  let iWU : W ⟶ U := Opens.infLELeft (U ⊓ V) B ≫ Opens.infLELeft U V
  let iWV : W ⟶ V := Opens.infLELeft (U ⊓ V) B ≫ Opens.infLERight U V
  refine ⟨W, hxW, iWU, iWV, fun w ↦ ?_⟩
  rw [hfval, hgval]
  apply he (positivePointIdeal 𝒜 w.1)
  rw [Ideal.mem_primeCompl_iff]
  have hwB : w.1 ∈ ProjectiveSpectrum.basicOpen 𝒜 (e : A) := w.2.2
  exact (ProjectiveSpectrum.mem_basicOpen 𝒜 (e : A) w.1).mp hwB

/-- Fixed positive fractions are stable under restriction. -/
def isPositiveSectionFractionPrelocal (m : ℕ) :
    PrelocalPredicate (PositiveFiber 𝒜) where
  pred f := IsPositiveSectionFraction 𝒜 m f
  res := by
    rintro U V i f (rfl | ⟨j, a, b, hb, h⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨j, a, b, fun x ↦ hb (i x), fun x ↦ h (i x)⟩

/-- The local positive-fraction predicate defining the positive twist. -/
def isLocallyPositiveSectionFraction (m : ℕ) :
    LocalPredicate (PositiveFiber 𝒜) :=
  (isPositiveSectionFractionPrelocal 𝒜 m).sheafify

/-- Locally positive homogeneous fractions which agree at a point agree on
a neighborhood of that point. -/
theorem isLocallyPositiveSectionFraction_eq_neighborhood (m : ℕ)
    {U V : Opens X} {f : ∀ y : U, PositiveFiber 𝒜 y.1}
    {g : ∀ y : V, PositiveFiber 𝒜 y.1}
    (hf : (isLocallyPositiveSectionFraction 𝒜 m).pred f)
    (hg : (isLocallyPositiveSectionFraction 𝒜 m).pred g)
    (x : X) (hxU : x ∈ U) (hxV : x ∈ V)
    (hx : f ⟨x, hxU⟩ = g ⟨x, hxV⟩) :
    ∃ (W : Opens X) (hxW : x ∈ W) (iWU : W ⟶ U) (iWV : W ⟶ V),
      ∀ w : W, f (iWU w) = g (iWV w) := by
  rcases hf ⟨x, hxU⟩ with ⟨U', hxU', iU, hf'⟩
  rcases hg ⟨x, hxV⟩ with ⟨V', hxV', iV, hg'⟩
  have hx' :
      f (iU ⟨x, hxU'⟩) = g (iV ⟨x, hxV'⟩) := by
    simpa using hx
  obtain ⟨W, hxW, iWU', iWV', hW⟩ :=
    isPositiveSectionFraction_eq_neighborhood 𝒜 m hf' hg' x hxU' hxV' hx'
  refine ⟨W, hxW, iWU' ≫ iU, iWV' ≫ iV, fun w ↦ ?_⟩
  exact hW w

theorem isPositiveSectionFraction_zero (m : ℕ) {U : Opens X} :
    IsPositiveSectionFraction 𝒜 m
      (0 : ∀ x : U, PositiveFiber 𝒜 x.1) :=
  Or.inl rfl

theorem isPositiveSectionFraction_add (m : ℕ) {U : Opens X}
    {f g : ∀ x : U, PositiveFiber 𝒜 x.1}
    (hf : IsPositiveSectionFraction 𝒜 m f)
    (hg : IsPositiveSectionFraction 𝒜 m g) :
    IsPositiveSectionFraction 𝒜 m (f + g) := by
  rcases hf with rfl | ⟨i, a, b, hb, hf⟩
  · simpa only [zero_add] using hg
  rcases hg with rfl | ⟨j, c, d, hd, hg⟩
  · rw [add_zero]
    exact Or.inr ⟨i, a, b, hb, hf⟩
  right
  let num : 𝒜 (m + (i + j)) := ⟨(a : A) * d + (c : A) * b, by
    apply AddMemClass.add_mem
    · have h : (a : A) * d ∈ 𝒜 ((m + i) + j) := mul_mem_graded a.2 d.2
      simpa only [add_assoc] using h
    · have h : (c : A) * b ∈ 𝒜 ((m + j) + i) := mul_mem_graded c.2 b.2
      simpa only [add_assoc, add_left_comm, add_comm] using h⟩
  let den : 𝒜 (i + j) := ⟨(b : A) * d, mul_mem_graded b.2 d.2⟩
  refine ⟨i + j, num, den, fun x ↦ ?_, fun x ↦ ?_⟩
  · exact x.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem (hb x) (hd x)
  · rw [Pi.add_apply, hf x, hg x, Localization.add_mk]
    congr 1
    ring

theorem isPositiveSectionFraction_neg (m : ℕ) {U : Opens X}
    {f : ∀ x : U, PositiveFiber 𝒜 x.1}
    (hf : IsPositiveSectionFraction 𝒜 m f) :
    IsPositiveSectionFraction 𝒜 m (-f) := by
  rcases hf with rfl | ⟨i, a, b, hb, hf⟩
  · exact Or.inl (neg_zero)
  right
  refine ⟨i, ⟨-(a : A), NegMemClass.neg_mem a.2⟩, b, hb, fun x ↦ ?_⟩
  rw [Pi.neg_apply, hf x]
  exact Localization.neg_mk _ _

set_option backward.isDefEq.respectTransparency.types false in
/-- Degree-zero structure-sheaf fractions act on positive fractions. -/
theorem isPositiveSectionFraction_smul (m : ℕ) {U : Opens X}
    {r : ∀ x : U, HomogeneousLocalization.AtPrime 𝒜
      (positivePointIdeal 𝒜 x.1)}
    {f : ∀ x : U, PositiveFiber 𝒜 x.1}
    (hr : ProjectiveSpectrum.StructureSheaf.IsFraction r)
    (hf : IsPositiveSectionFraction 𝒜 m f) :
    IsPositiveSectionFraction 𝒜 m (fun x ↦ r x • f x) := by
  rcases hf with rfl | ⟨i, a, b, hb, hf⟩
  · exact Or.inl (funext fun x ↦ smul_zero (r x))
  rcases hr with ⟨j, c, d, hd, hr⟩
  right
  let num : 𝒜 (m + (j + i)) := ⟨(c : A) * a, by
    have h : (c : A) * a ∈ 𝒜 (j + (m + i)) := mul_mem_graded c.2 a.2
    simpa only [add_assoc, add_left_comm, add_comm] using h⟩
  let den : 𝒜 (j + i) := ⟨(d : A) * b, mul_mem_graded d.2 b.2⟩
  refine ⟨j + i, num, den, fun x ↦ ?_, fun x ↦ ?_⟩
  · exact x.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem (hd x) (hb x)
  · change r x • f x = _
    rw [hr x, hf x]
    change (HomogeneousLocalization.mk _).val * Localization.mk (a : A) _ =
      Localization.mk ((c : A) * a) _
    rw [HomogeneousLocalization.val_mk, Localization.mk_mul]
    congr 1

theorem isLocallyPositiveSectionFraction_zero (m : ℕ) {U : Opens X} :
    (isLocallyPositiveSectionFraction 𝒜 m).pred
      (0 : ∀ x : U, PositiveFiber 𝒜 x.1) :=
  (isPositiveSectionFractionPrelocal 𝒜 m).sheafifyOf
    (isPositiveSectionFraction_zero 𝒜 m)

theorem isLocallyPositiveSectionFraction_add (m : ℕ) {U : Opens X}
    {f g : ∀ x : U, PositiveFiber 𝒜 x.1}
    (hf : (isLocallyPositiveSectionFraction 𝒜 m).pred f)
    (hg : (isLocallyPositiveSectionFraction 𝒜 m).pred g) :
    (isLocallyPositiveSectionFraction 𝒜 m).pred (f + g) :=
  (isPositiveSectionFractionPrelocal 𝒜 m).sheafify_inductionOn₂'
    (isPositiveSectionFractionPrelocal 𝒜 m)
    (isPositiveSectionFractionPrelocal 𝒜 m)
    (fun a b ↦ a + b)
    (fun {U V} {a b} ha hb ↦
      isPositiveSectionFraction_add 𝒜 m
        ((isPositiveSectionFractionPrelocal 𝒜 m).res (Opens.infLELeft U V) a ha)
        ((isPositiveSectionFractionPrelocal 𝒜 m).res (Opens.infLERight U V) b hb)) hf hg

theorem isLocallyPositiveSectionFraction_neg (m : ℕ) {U : Opens X}
    {f : ∀ x : U, PositiveFiber 𝒜 x.1}
    (hf : (isLocallyPositiveSectionFraction 𝒜 m).pred f) :
    (isLocallyPositiveSectionFraction 𝒜 m).pred (-f) :=
  (isPositiveSectionFractionPrelocal 𝒜 m).sheafify_inductionOn'
    (fun a ↦ -a) (fun ha ↦ isPositiveSectionFraction_neg 𝒜 m ha) hf

set_option backward.isDefEq.respectTransparency.types false in
theorem isLocallyPositiveSectionFraction_smul (m : ℕ) {U : Opens X}
    {r : ∀ x : U, HomogeneousLocalization.AtPrime 𝒜
      (positivePointIdeal 𝒜 x.1)}
    {f : ∀ x : U, PositiveFiber 𝒜 x.1}
    (hr : (ProjectiveSpectrum.StructureSheaf.isLocallyFraction 𝒜).pred r)
    (hf : (isLocallyPositiveSectionFraction 𝒜 m).pred f) :
    (isLocallyPositiveSectionFraction 𝒜 m).pred (fun x ↦ r x • f x) :=
  (ProjectiveSpectrum.StructureSheaf.isFractionPrelocal 𝒜).sheafify_inductionOn₂'
    (isPositiveSectionFractionPrelocal 𝒜 m)
    (isPositiveSectionFractionPrelocal 𝒜 m)
    (fun a b ↦ a • b)
    (fun {U V} {a b} ha hb ↦
      isPositiveSectionFraction_smul 𝒜 m
        ((ProjectiveSpectrum.StructureSheaf.isFractionPrelocal 𝒜).res
          (Opens.infLELeft U V) a ha)
        ((isPositiveSectionFractionPrelocal 𝒜 m).res (Opens.infLERight U V) b hb)) hr hf

/-- Multiplication pairs a fixed positive fraction with a fixed negative
fraction of the same degree to a fixed degree-zero fraction. -/
theorem isPositiveSectionFraction_mul_negativeSectionFraction (m : ℕ)
    {U : Opens X} {f g : ∀ x : U, PositiveFiber 𝒜 x.1}
    (hf : IsPositiveSectionFraction 𝒜 m f)
    (hg : IsSectionFraction 𝒜 m g) :
    IsSectionFraction 𝒜 0 (fun x ↦ f x * g x) := by
  rcases hf with rfl | ⟨i, a, b, hb, hf⟩
  · exact Or.inl (funext fun x ↦ zero_mul (g x))
  rcases hg with rfl | ⟨j, c, d, hd, hg⟩
  · exact Or.inl (funext fun x ↦ mul_zero (f x))
  right
  let k := m + i + j
  let num : 𝒜 k := ⟨(a : A) * c, by
    have h : (a : A) * c ∈ 𝒜 ((m + i) + j) := mul_mem_graded a.2 c.2
    simpa only [k, add_assoc] using h⟩
  let den : 𝒜 (k + 0) := ⟨(b : A) * d, by
    have h : (b : A) * d ∈ 𝒜 (i + (j + m)) := mul_mem_graded b.2 d.2
    simpa only [k, add_zero, add_assoc, add_left_comm, add_comm] using h⟩
  refine ⟨k, num, den, fun x ↦ ?_, fun x ↦ ?_⟩
  · exact x.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem (hb x) (hd x)
  · change f x * g x = _
    rw [hf x, hg x, Localization.mk_mul]
    congr 1

/-- The positive/negative fraction pairing is stable under local gluing. -/
theorem isLocallyPositiveSectionFraction_mul_locallySectionFraction (m : ℕ)
    {U : Opens X} {f g : ∀ x : U, PositiveFiber 𝒜 x.1}
    (hf : (isLocallyPositiveSectionFraction 𝒜 m).pred f)
    (hg : (isLocallySectionFraction 𝒜 m).pred g) :
    (isLocallySectionFraction 𝒜 0).pred (fun x ↦ f x * g x) := by
  intro x
  rcases hf x with ⟨V, hxV, iV, hV⟩
  rcases hg x with ⟨W, hxW, iW, hW⟩
  let Z := V ⊓ W
  let iZV : Z ⟶ V := Opens.infLELeft V W
  let iZW : Z ⟶ W := Opens.infLERight V W
  have hxZ : x.1 ∈ Z := ⟨hxV, hxW⟩
  refine ⟨Z, hxZ, iZV ≫ iV, ?_⟩
  exact isPositiveSectionFraction_mul_negativeSectionFraction 𝒜 m
    ((isPositiveSectionFractionPrelocal 𝒜 m).res iZV _ hV)
    ((isSectionFractionPrelocal 𝒜 m).res iZW _ hW)

/-- Multiplication by a homogeneous form of degree `d` sends a positive
degree-`m` fraction to a positive degree-`(m+d)` fraction. -/
theorem isPositiveSectionFraction_mulHomogeneous {d : ℕ} (s : 𝒜 d) (m : ℕ)
    {U : Opens X} {f : ∀ x : U, PositiveFiber 𝒜 x.1}
    (hf : IsPositiveSectionFraction 𝒜 m f) :
    IsPositiveSectionFraction 𝒜 (m + d)
      (fun x ↦ algebraMap A (PositiveFiber 𝒜 x.1) (s : A) * f x) := by
  rcases hf with rfl | ⟨i, a, b, hb, hf⟩
  · exact Or.inl (funext fun x ↦ mul_zero _)
  right
  let num : 𝒜 ((m + d) + i) := ⟨(s : A) * a, by
    have h : (s : A) * a ∈ 𝒜 (d + (m + i)) := mul_mem_graded s.2 a.2
    simpa only [add_assoc, add_left_comm, add_comm] using h⟩
  refine ⟨i, num, b, hb, fun x ↦ ?_⟩
  change algebraMap A (PositiveFiber 𝒜 x.1) (s : A) * f x = _
  rw [hf x, ← Localization.mk_one_eq_algebraMap, Localization.mk_mul]
  congr 1
  apply Subtype.ext
  simp only [one_mul]

/-- Homogeneous multiplication preserves the local positive-fraction
predicate. -/
theorem isLocallyPositiveSectionFraction_mulHomogeneous {d : ℕ}
    (s : 𝒜 d) (m : ℕ) {U : Opens X}
    {f : ∀ x : U, PositiveFiber 𝒜 x.1}
    (hf : (isLocallyPositiveSectionFraction 𝒜 m).pred f) :
    (isLocallyPositiveSectionFraction 𝒜 (m + d)).pred
      (fun x ↦ algebraMap A (PositiveFiber 𝒜 x.1) (s : A) * f x) := by
  intro x
  rcases hf x with ⟨V, hxV, i, hV⟩
  exact ⟨V, hxV, i,
    isPositiveSectionFraction_mulHomogeneous 𝒜 s m hV⟩

set_option backward.isDefEq.respectTransparency false in
/-- Positive local fractions form a module over the structure sheaf. -/
def positiveSectionsSubmodule (m : ℕ) (U : Opens X) :
    Submodule (ProjectiveSpectrum.StructureSheaf.sectionsSubring (op U))
      (∀ x : U, PositiveFiber 𝒜 x.1) where
  carrier := {f | (isLocallyPositiveSectionFraction 𝒜 m).pred f}
  zero_mem' := isLocallyPositiveSectionFraction_zero 𝒜 m
  add_mem' hf hg := isLocallyPositiveSectionFraction_add 𝒜 m hf hg
  smul_mem' r f hf := by
    change (isLocallyPositiveSectionFraction 𝒜 m).pred (fun x ↦ r.1 x • f x)
    exact isLocallyPositiveSectionFraction_smul 𝒜 m r.2 hf

/-- The underlying type-valued positive twist sheaf. -/
def positiveSheafInType (m : ℕ) : Sheaf (Type u) X :=
  subsheafToTypes (isLocallyPositiveSectionFraction 𝒜 m)

instance positiveSheafInTypeAddCommGroup (m : ℕ) (U : (Opens X)ᵒᵖ) :
    AddCommGroup ((positiveSheafInType 𝒜 m).1.obj U) :=
  (positiveSectionsSubmodule 𝒜 m U.unop).toAddSubgroup.toAddCommGroup

instance positiveSheafInTypeModule (m : ℕ) (U : (Opens X)ᵒᵖ) :
    Module ((ProjectiveSpectrum.Proj.structureSheaf 𝒜).1.obj U)
      ((positiveSheafInType 𝒜 m).1.obj U) :=
  inferInstanceAs
    (Module (ProjectiveSpectrum.StructureSheaf.sectionsSubring U)
      (positiveSectionsSubmodule 𝒜 m U.unop))

/-- The additive presheaf underlying the positive twist. -/
def positivePresheafInAddCommGrp (m : ℕ) : Presheaf AddCommGrpCat X where
  obj U := AddCommGrpCat.of ((positiveSheafInType 𝒜 m).1.obj U)
  map i := AddCommGrpCat.ofHom
    { toFun := (positiveSheafInType 𝒜 m).1.map i
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }

set_option backward.isDefEq.respectTransparency false in
/-- The positive projective twist as a presheaf of modules. -/
def positiveModulePresheaf (m : ℕ) : (Proj 𝒜).PresheafOfModules := by
  letI (U : (Opens (Proj 𝒜))ᵒᵖ) :
      Module ((Proj 𝒜).ringCatSheaf.obj.obj U)
        ((positivePresheafInAddCommGrp 𝒜 m).obj U) := by
    change Module ((ProjectiveSpectrum.Proj.structureSheaf 𝒜).1.obj U)
      ((positiveSheafInType 𝒜 m).1.obj U)
    infer_instance
  exact PresheafOfModules.ofPresheaf (positivePresheafInAddCommGrp 𝒜 m)
    (fun _ _ _ _ _ ↦ rfl)

/-- The positive projective twisting sheaf obtained from locally homogeneous
fractions of degree `m`. -/
def positiveSheafOfModules (m : ℕ) : (Proj 𝒜).Modules where
  val := positiveModulePresheaf 𝒜 m
  isSheaf := by
    apply (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat) _).2
    change Presheaf.IsSheaf (positiveSheafInType 𝒜 m).1
    exact (positiveSheafInType 𝒜 m).2

/-- Degree-zero positive and negative fixed-fraction predicates coincide. -/
theorem isPositiveSectionFraction_zero_iff_isSectionFraction_zero
    {U : Opens X} {f : ∀ x : U, PositiveFiber 𝒜 x.1} :
    IsPositiveSectionFraction 𝒜 0 f ↔ IsSectionFraction 𝒜 0 f := by
  constructor
  · intro hf
    rcases hf with hzero | ⟨i, a, b, hb, h⟩
    · exact Or.inl hzero
    · right
      refine ⟨i, ⟨(a : A), by simpa using a.2⟩,
        ⟨(b : A), by simpa using b.2⟩, hb, ?_⟩
      simpa using h
  · intro hf
    rcases hf with hzero | ⟨i, a, b, hb, h⟩
    · exact Or.inl hzero
    · right
      refine ⟨i, ⟨(a : A), by simpa using a.2⟩,
        ⟨(b : A), by simpa using b.2⟩, hb, ?_⟩
      simpa using h

/-- The local degree-zero positive predicate is the already constructed
degree-zero negative predicate. -/
theorem isLocallyPositiveSectionFraction_zero_iff_isLocallySectionFraction_zero
    {U : Opens X} {f : ∀ x : U, PositiveFiber 𝒜 x.1} :
    (isLocallyPositiveSectionFraction 𝒜 0).pred f ↔
      (isLocallySectionFraction 𝒜 0).pred f := by
  constructor <;> intro h x
  · rcases h x with ⟨V, hxV, i, hV⟩
    exact ⟨V, hxV, i,
      (isPositiveSectionFraction_zero_iff_isSectionFraction_zero (𝒜 := 𝒜)).mp hV⟩
  · rcases h x with ⟨V, hxV, i, hV⟩
    exact ⟨V, hxV, i,
      (isPositiveSectionFraction_zero_iff_isSectionFraction_zero (𝒜 := 𝒜)).mpr hV⟩

set_option backward.isDefEq.respectTransparency false in
/-- The positive concrete zero twist maps identically to the negative
concrete zero twist. -/
def positiveZeroToZeroTwist :
    positiveSheafOfModules 𝒜 0 ⟶ sheafOfModules 𝒜 0 where
  val :=
    { app := fun U => by
        letI : Module ((Proj 𝒜).ringCatSheaf.obj.obj U)
            ((positivePresheafInAddCommGrp 𝒜 0).obj U) := by
          change Module ((ProjectiveSpectrum.Proj.structureSheaf 𝒜).1.obj U)
            ((positiveSheafInType 𝒜 0).1.obj U)
          infer_instance
        letI : Module ((Proj 𝒜).ringCatSheaf.obj.obj U)
            ((presheafInAddCommGrp 𝒜 0).obj U) := by
          change Module ((ProjectiveSpectrum.Proj.structureSheaf 𝒜).1.obj U)
            ((sheafInType 𝒜 0).1.obj U)
          infer_instance
        exact ModuleCat.ofHom
          { toFun := fun z ↦ ⟨z.1,
              (isLocallyPositiveSectionFraction_zero_iff_isLocallySectionFraction_zero
                (𝒜 := 𝒜)).mp z.2⟩
            map_add' := fun _ _ ↦ rfl
            map_smul' := fun _ _ ↦ rfl }
      naturality := by
        intro U V i
        ext z
        rfl }

set_option backward.isDefEq.respectTransparency false in
/-- The reverse identity map between the two concrete zero twists. -/
def zeroTwistToPositiveZero :
    sheafOfModules 𝒜 0 ⟶ positiveSheafOfModules 𝒜 0 where
  val :=
    { app := fun U => by
        letI : Module ((Proj 𝒜).ringCatSheaf.obj.obj U)
            ((presheafInAddCommGrp 𝒜 0).obj U) := by
          change Module ((ProjectiveSpectrum.Proj.structureSheaf 𝒜).1.obj U)
            ((sheafInType 𝒜 0).1.obj U)
          infer_instance
        letI : Module ((Proj 𝒜).ringCatSheaf.obj.obj U)
            ((positivePresheafInAddCommGrp 𝒜 0).obj U) := by
          change Module ((ProjectiveSpectrum.Proj.structureSheaf 𝒜).1.obj U)
            ((positiveSheafInType 𝒜 0).1.obj U)
          infer_instance
        exact ModuleCat.ofHom
          { toFun := fun z ↦ ⟨z.1,
              (isLocallyPositiveSectionFraction_zero_iff_isLocallySectionFraction_zero
                (𝒜 := 𝒜)).mpr z.2⟩
            map_add' := fun _ _ ↦ rfl
            map_smul' := fun _ _ ↦ rfl }
      naturality := by
        intro U V i
        ext z
        rfl }

/-- The two concrete degree-zero twist constructions are canonically
isomorphic. -/
noncomputable def positiveZeroTwistIso :
    positiveSheafOfModules 𝒜 0 ≅ sheafOfModules 𝒜 0 where
  hom := positiveZeroToZeroTwist 𝒜
  inv := zeroTwistToPositiveZero 𝒜
  hom_inv_id := by
    ext U z x
    rfl
  inv_hom_id := by
    ext U z x
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- Multiplication by a homogeneous form as a morphism of positive twisting
sheaves, `O(m) ⟶ O(m+d)`. -/
def positiveMulHomogeneous {d : ℕ} (s : 𝒜 d) (m : ℕ) :
    positiveSheafOfModules 𝒜 m ⟶ positiveSheafOfModules 𝒜 (m + d) where
  val :=
    { app := fun U => by
        letI : Module ((Proj 𝒜).ringCatSheaf.obj.obj U)
            ((positivePresheafInAddCommGrp 𝒜 m).obj U) := by
          change Module ((ProjectiveSpectrum.Proj.structureSheaf 𝒜).1.obj U)
            ((positiveSheafInType 𝒜 m).1.obj U)
          infer_instance
        letI : Module ((Proj 𝒜).ringCatSheaf.obj.obj U)
            ((positivePresheafInAddCommGrp 𝒜 (m + d)).obj U) := by
          change Module ((ProjectiveSpectrum.Proj.structureSheaf 𝒜).1.obj U)
            ((positiveSheafInType 𝒜 (m + d)).1.obj U)
          infer_instance
        exact ModuleCat.ofHom
          { toFun := fun f ↦
              ⟨fun x ↦ algebraMap A (PositiveFiber 𝒜 x.1) (s : A) * f.1 x,
                isLocallyPositiveSectionFraction_mulHomogeneous 𝒜 s m f.2⟩
            map_add' := fun f g ↦ by
              apply Subtype.ext
              funext x
              exact mul_add _ _ _
            map_smul' := fun r f ↦ by
              apply Subtype.ext
              funext x
              change algebraMap A (PositiveFiber 𝒜 x.1) (s : A) *
                    ((r.1 x).val * f.1 x) =
                (r.1 x).val *
                  (algebraMap A (PositiveFiber 𝒜 x.1) (s : A) * f.1 x)
              ring }
      naturality := by
        intro U V i
        ext f
        rfl }

set_option backward.isDefEq.respectTransparency false in
/-- Over a domain, multiplication by a nonzero homogeneous form is injective
on every open set of a positive twist. -/
theorem positiveMulHomogeneous_app_injective [IsDomain A] {d : ℕ} (s : 𝒜 d)
    (hs : (s : A) ≠ 0) (m : ℕ) (U : (Opens (Proj 𝒜))ᵒᵖ) :
    Function.Injective ((positiveMulHomogeneous 𝒜 s m).val.app U) := by
  intro f g hfg
  apply Subtype.ext
  funext x
  have hx := congr_fun (congr_arg Subtype.val hfg) x
  apply mul_left_cancel₀ _ hx
  intro hzero
  apply hs
  apply IsLocalization.injective (PositiveFiber 𝒜 x.1)
    (positivePointIdeal 𝒜 x.1).primeCompl_le_nonZeroDivisors
  simpa using hzero

/-- Over a domain, multiplication by a nonzero homogeneous form is a
monomorphism of positive twisting sheaves. -/
theorem positiveMulHomogeneous_mono [IsDomain A] {d : ℕ} (s : 𝒜 d)
    (hs : (s : A) ≠ 0) (m : ℕ) :
    Mono (positiveMulHomogeneous 𝒜 s m) := by
  apply (SheafOfModules.forget (Proj 𝒜).ringCatSheaf).mono_of_mono_map
  exact PresheafOfModules.mono_of_injective
    (fun {U} ↦ positiveMulHomogeneous_app_injective 𝒜 s hs m U)

set_option backward.isDefEq.respectTransparency false in
/-- The presheaf-level multiplication pairing between the positive and
negative twists of the same degree. -/
noncomputable def positiveNegativePairingPresheaf (m : ℕ) :
    PresheafOfModules.Monoidal.tensorObj (R := (Proj 𝒜).sheaf.obj)
      (positiveModulePresheaf 𝒜 m) (modulePresheaf 𝒜 m) ⟶
      modulePresheaf 𝒜 0 where
  app U := ModuleCat.MonoidalCategory.tensorLift
    (fun p q ↦
      ⟨fun x ↦ p.1 x * q.1 x,
        isLocallyPositiveSectionFraction_mul_locallySectionFraction 𝒜 m
          p.2 q.2⟩)
    (by
      intro p q r
      apply Subtype.ext
      funext x
      exact add_mul _ _ _)
    (by
      intro r p q
      apply Subtype.ext
      funext x
      change ((r.1 x).val * p.1 x) * q.1 x =
        (r.1 x).val * (p.1 x * q.1 x)
      ring)
    (by
      intro p q r
      apply Subtype.ext
      funext x
      exact mul_add _ _ _)
    (by
      intro r p q
      apply Subtype.ext
      funext x
      change p.1 x * ((r.1 x).val * q.1 x) =
        (r.1 x).val * (p.1 x * q.1 x)
      ring)
  naturality := by
    intro U V i
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro p q
    apply Subtype.ext
    funext x
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- Multiplication by a homogeneous form can be shifted between the two
factors of the positive/negative fraction pairing. -/
theorem positiveNegativePairingPresheaf_mul_naturality {d : ℕ}
    (s : 𝒜 d) (m : ℕ) :
    PresheafOfModules.Monoidal.tensorHom (positiveMulHomogeneous 𝒜 s m).val
      (𝟙 (modulePresheaf 𝒜 (m + d))) ≫ positiveNegativePairingPresheaf 𝒜 (m + d) =
    PresheafOfModules.Monoidal.tensorHom (𝟙 (positiveModulePresheaf 𝒜 m))
      (mulHomogeneous 𝒜 s m).val ≫ positiveNegativePairingPresheaf 𝒜 m := by
  ext1 U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro p q
  apply Subtype.ext
  funext x
  change (algebraMap A (PositiveFiber 𝒜 x.1) (s : A) * p.1 x) * q.1 x =
    p.1 x * (algebraMap A (PositiveFiber 𝒜 x.1) (s : A) * q.1 x)
  ring

/-- The sheaf-level multiplication pairing
`O(m) ⊗ O(-m) ⟶ O(0)`.  It is obtained from the pointwise fraction pairing
by the universal property of module-sheafification. -/
noncomputable def positiveNegativePairing (m : ℕ) :
    schemeModuleTensor (positiveSheafOfModules 𝒜 m) (sheafOfModules 𝒜 m) ⟶
      sheafOfModules 𝒜 0 :=
  ((PresheafOfModules.sheafificationAdjunction
    (𝟙 (Proj 𝒜).ringCatSheaf.obj)).homEquiv _ _).symm
      (positiveNegativePairingPresheaf 𝒜 m)

/-- Multiplication by a homogeneous form may be shifted between the two
factors of the sheaf-level positive/negative pairing. -/
theorem positiveNegativePairing_mul_naturality {d : ℕ}
    (s : 𝒜 d) (m : ℕ) :
    schemeModuleTensorMap (positiveMulHomogeneous 𝒜 s m)
      (𝟙 (sheafOfModules 𝒜 (m + d))) ≫ positiveNegativePairing 𝒜 (m + d) =
    schemeModuleTensorMap (𝟙 (positiveSheafOfModules 𝒜 m))
      (mulHomogeneous 𝒜 s m) ≫ positiveNegativePairing 𝒜 m := by
  rw [schemeModuleTensorMap_eq_sheafification,
    schemeModuleTensorMap_eq_sheafification]
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 (Proj 𝒜).ringCatSheaf.obj)
  have hpair (n : ℕ) :
      adj.homEquiv
        (PresheafOfModules.Monoidal.tensorObj (positiveSheafOfModules 𝒜 n).val
          (sheafOfModules 𝒜 n).val) (sheafOfModules 𝒜 0)
        (positiveNegativePairing 𝒜 n) =
      positiveNegativePairingPresheaf 𝒜 n := by
    exact (adj.homEquiv _ _).apply_symm_apply _
  apply (adj.homEquiv _ _).injective
  erw [adj.homEquiv_naturality_left]
  rw [hpair]
  erw [adj.homEquiv_naturality_left]
  rw [hpair]
  exact positiveNegativePairingPresheaf_mul_naturality 𝒜 s m

/-- Evaluation of a positive-twist section at a point. -/
def positiveSectionValue (m : ℕ) (U : (Opens X)ᵒᵖ)
    (z : (positiveSheafOfModules 𝒜 m).val.obj U) (x : U.unop) :
    positiveStalkSubmodule 𝒜 (positivePointIdeal 𝒜 x.1) m := by
  refine ⟨z.1 x, ?_⟩
  rcases z.2 x with ⟨V, hxV, i, hV⟩
  rcases hV with hzero | ⟨j, a, b, hb, hval⟩
  · left
    simpa using congr_fun hzero ⟨x.1, hxV⟩
  · right
    refine ⟨j, a, b, ?_, ?_⟩
    · simpa using hb ⟨x.1, hxV⟩
    · simpa using hval ⟨x.1, hxV⟩

/-- The positive homogeneous-fraction section on the basic open of its
homogeneous denominator. -/
def positiveSectionInBasicOpen (m i : ℕ) (a : 𝒜 (m + i)) (b : 𝒜 i) :
    (positiveModulePresheaf 𝒜 m).presheaf.obj
      (op (ProjectiveSpectrum.basicOpen 𝒜 (b : A))) := by
  let hb : ∀ y : ProjectiveSpectrum.basicOpen 𝒜 (b : A),
      (b : A) ∈ (positivePointIdeal 𝒜 y.1).primeCompl := fun y ↦ by
    rw [Ideal.mem_primeCompl_iff]
    exact (ProjectiveSpectrum.mem_basicOpen 𝒜 (b : A) y.1).mp y.2
  exact ⟨fun y ↦ Localization.mk (a : A) ⟨(b : A), hb y⟩,
    (isPositiveSectionFractionPrelocal 𝒜 m).sheafifyOf
      (Or.inr ⟨i, a, b, hb, fun _ ↦ rfl⟩)⟩

/-- A homogeneous element of degree `m` defines a genuine global section of
the positive twist `O(m)`.  It is the fraction with denominator `1`; the
definition first realizes it on `D_+(1)=Proj` and then packages its
restrictions as a compatible family. -/
noncomputable def positiveGlobalSectionOfHomogeneous (m : ℕ) (a : 𝒜 m) :
    (positiveSheafOfModules 𝒜 m).sections := by
  let M := positiveSheafOfModules 𝒜 m
  let b : 𝒜 0 := 1
  have hb : (b : A) = 1 := rfl
  have hU : ProjectiveSpectrum.basicOpen 𝒜 (b : A) = ⊤ := by
    rw [hb]
    exact ProjectiveSpectrum.basicOpen_one 𝒜
  let sTop : M.val.obj (op (⊤ : Opens (Proj 𝒜))) :=
    M.val.map (eqToHom hU.symm).op
      (positiveSectionInBasicOpen 𝒜 m 0 (by simpa using a) b)
  exact M.val.sectionsMk
    (fun U ↦ M.val.map
      (homOfLE (show U.unop ≤ (⊤ : Opens (Proj 𝒜)) from le_top)).op sTop)
    (by
      intro U V f
      rw [← M.val.map_comp_apply]
      congr)

/-- The global section defined by a homogeneous element has the expected
value at every projective point: in the homogeneous-fraction stalk it is the
fraction `a / 1`.  This is the concrete evaluation identity used when the
sheaf-theoretic restriction map is compared with polynomial evaluation on a
finite projective subscheme. -/
theorem positiveSectionValue_positiveGlobalSectionOfHomogeneous
    (m : ℕ) (a : 𝒜 m) (x : X) :
    (positiveSectionValue 𝒜 m (op (⊤ : Opens X))
        (PresheafOfModules.sections.eval
          (positiveGlobalSectionOfHomogeneous 𝒜 m a)
          (op (⊤ : Opens X))) ⟨x, trivial⟩).1 =
      Localization.mk (a : A) ⟨1, Submonoid.one_mem _⟩ := by
  rfl

/-- Evaluation at a point, as an additive map from positive-twist sections. -/
def positiveSectionValueAddMonoidHom (m : ℕ) (U : (Opens X)ᵒᵖ) (x : U.unop) :
    ((positiveModulePresheaf 𝒜 m).presheaf.obj U) →+
      positiveStalkSubmodule 𝒜 (positivePointIdeal 𝒜 x.1) m where
  toFun z := positiveSectionValue 𝒜 m U z x
  map_zero' := by
    apply Subtype.ext
    rfl
  map_add' z w := by
    apply Subtype.ext
    rfl

/-- The evaluation cocone for the positive-twist stalk. -/
def positiveFractionModuleCocone (m : ℕ) (x : X) :
    Cocone ((OpenNhds.inclusion x).op ⋙ (positiveModulePresheaf 𝒜 m).presheaf) where
  pt := AddCommGrpCat.of (positiveStalkSubmodule 𝒜 (positivePointIdeal 𝒜 x) m)
  ι :=
    { app := fun U ↦ AddCommGrpCat.ofHom
        (positiveSectionValueAddMonoidHom 𝒜 m (op (unop U).1) ⟨x, (unop U).2⟩) }

/-- Evaluation of positive germs in the concrete homogeneous-fraction stalk. -/
def positiveStalkToFractionModule (m : ℕ) (x : X) :
    (↑(TopCat.Presheaf.stalk (C := AddCommGrpCat)
      (positiveModulePresheaf 𝒜 m).presheaf x) : Type u) →+
      positiveStalkSubmodule 𝒜 (positivePointIdeal 𝒜 x) m :=
  (colimit.desc _ (positiveFractionModuleCocone 𝒜 m x)).hom

@[simp]
theorem positiveStalkToFractionModule_germ (m : ℕ) (U : Opens X)
    (x : X) (hx : x ∈ U)
    (z : (positiveModulePresheaf 𝒜 m).presheaf.obj (op U)) :
    positiveStalkToFractionModule 𝒜 m x
        (TopCat.Presheaf.germ (C := AddCommGrpCat)
          (positiveModulePresheaf 𝒜 m).presheaf U x hx z) =
      positiveSectionValue 𝒜 m (op U) z ⟨x, hx⟩ := by
  dsimp [positiveStalkToFractionModule, Presheaf.germ]
  exact CategoryTheory.Limits.colimit.ι_desc_apply _ _ _

/-- Evaluation is injective on the categorical positive-twist stalk. -/
theorem positiveStalkToFractionModule_injective (m : ℕ) (x : X) :
    Function.Injective (positiveStalkToFractionModule 𝒜 m x) := by
  intro z w hzw
  obtain ⟨U, hxU, zU, rfl⟩ :=
    TopCat.Presheaf.exists_germ_eq (positiveModulePresheaf 𝒜 m).presheaf z
  obtain ⟨V, hxV, wV, rfl⟩ :=
    TopCat.Presheaf.exists_germ_eq (positiveModulePresheaf 𝒜 m).presheaf w
  have hz := positiveStalkToFractionModule_germ 𝒜 m U x hxU zU
  have hw := positiveStalkToFractionModule_germ 𝒜 m V x hxV wV
  have hsections := hz.symm.trans (hzw.trans hw)
  have hx : zU.1 ⟨x, hxU⟩ = wV.1 ⟨x, hxV⟩ :=
    congr_arg Subtype.val hsections
  obtain ⟨W, hxW, iWU, iWV, hW⟩ :=
    isLocallyPositiveSectionFraction_eq_neighborhood 𝒜 m zU.2 wV.2 x hxU hxV hx
  apply TopCat.Presheaf.germ_ext (positiveModulePresheaf 𝒜 m).presheaf
    W hxW iWU iWV
  apply Subtype.ext
  funext y
  exact hW y

/-- Every concrete positive homogeneous fraction is represented by a germ. -/
theorem positiveStalkToFractionModule_surjective (m : ℕ) (x : X) :
    Function.Surjective (positiveStalkToFractionModule 𝒜 m x) := by
  rintro ⟨z, hz⟩
  rcases hz with rfl | ⟨i, a, b, hb, rfl⟩
  · let U : Opens X := ⊤
    have hxU : x ∈ U := trivial
    let zU : (positiveModulePresheaf 𝒜 m).presheaf.obj (op U) := 0
    refine ⟨TopCat.Presheaf.germ (C := AddCommGrpCat)
      (positiveModulePresheaf 𝒜 m).presheaf U x hxU zU, ?_⟩
    calc
      _ = positiveSectionValue 𝒜 m (op U) zU ⟨x, hxU⟩ :=
        positiveStalkToFractionModule_germ 𝒜 m U x hxU zU
      _ = ⟨0, positiveFraction_zero_mem 𝒜 (positivePointIdeal 𝒜 x) m⟩ :=
        Subtype.ext rfl
  · let U := ProjectiveSpectrum.basicOpen 𝒜 (b : A)
    have hxU : x ∈ U := by
      change (b : A) ∉ x.asHomogeneousIdeal
      exact hb
    let zU := positiveSectionInBasicOpen 𝒜 m i a b
    refine ⟨TopCat.Presheaf.germ (C := AddCommGrpCat)
      (positiveModulePresheaf 𝒜 m).presheaf U x hxU zU, ?_⟩
    calc
      _ = positiveSectionValue 𝒜 m (op U) zU ⟨x, hxU⟩ :=
        positiveStalkToFractionModule_germ 𝒜 m U x hxU zU
      _ = ⟨Localization.mk (a : A) ⟨(b : A), hb⟩,
          Or.inr ⟨i, a, b, hb, rfl⟩⟩ := Subtype.ext rfl

/-- The categorical stalk of the positive twist is the concrete positive
homogeneous-fraction module. -/
def positiveStalkAddEquivFractionModule (m : ℕ) (x : X) :
    (↑(TopCat.Presheaf.stalk (C := AddCommGrpCat)
      (positiveModulePresheaf 𝒜 m).presheaf x) : Type u) ≃+
      positiveStalkSubmodule 𝒜 (positivePointIdeal 𝒜 x) m :=
  AddEquiv.ofBijective (positiveStalkToFractionModule 𝒜 m x)
    ⟨positiveStalkToFractionModule_injective 𝒜 m x,
      positiveStalkToFractionModule_surjective 𝒜 m x⟩

/-- The additive presheaf map underlying positive homogeneous
multiplication. -/
def positiveMulHomogeneousPresheaf {d : ℕ} (s : 𝒜 d) (m : ℕ) :
    (positiveModulePresheaf 𝒜 m).presheaf ⟶
      (positiveModulePresheaf 𝒜 (m + d)).presheaf :=
  (PresheafOfModules.toPresheaf _).map (positiveMulHomogeneous 𝒜 s m).val

/-- Evaluation commutes with positive homogeneous multiplication. -/
theorem positiveSectionValue_mulHomogeneous {d : ℕ} (s : 𝒜 d) (m : ℕ)
    (U : (Opens X)ᵒᵖ)
    (z : (positiveSheafOfModules 𝒜 m).val.obj U) (x : U.unop) :
    positiveSectionValue 𝒜 (m + d) U
        ((positiveMulHomogeneous 𝒜 s m).val.app U z) x =
      positiveMulHomogeneousStalk 𝒜 (positivePointIdeal 𝒜 x.1) s m
        (positiveSectionValue 𝒜 m U z x) :=
  rfl

/-- Evaluation identifies the categorical stalk map of positive homogeneous
multiplication with its concrete homogeneous-fraction counterpart. -/
theorem positiveStalkToFractionModule_stalkMap {d : ℕ} (s : 𝒜 d) (m : ℕ)
    (x : X)
    (z : ↑(TopCat.Presheaf.stalk (C := AddCommGrpCat)
      (positiveModulePresheaf 𝒜 m).presheaf x)) :
    positiveStalkToFractionModule 𝒜 (m + d) x
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          (positiveMulHomogeneousPresheaf 𝒜 s m) z) =
      positiveMulHomogeneousStalk 𝒜 (positivePointIdeal 𝒜 x) s m
        (positiveStalkToFractionModule 𝒜 m x z) := by
  obtain ⟨U, hxU, zU, rfl⟩ := TopCat.Presheaf.exists_germ_eq
    (positiveModulePresheaf 𝒜 m).presheaf z
  have hmap := TopCat.Presheaf.stalkFunctor_map_germ_apply U x hxU
    (positiveMulHomogeneousPresheaf 𝒜 s m) zU
  have happ :
      (positiveMulHomogeneousPresheaf 𝒜 s m).app (op U) zU =
        (positiveMulHomogeneous 𝒜 s m).val.app (op U) zU :=
    PresheafOfModules.toPresheaf_map_app_apply
      (positiveMulHomogeneous 𝒜 s m).val (op U) zU
  have hmap' :
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          (positiveMulHomogeneousPresheaf 𝒜 s m)
          (TopCat.Presheaf.germ (C := AddCommGrpCat)
            (positiveModulePresheaf 𝒜 m).presheaf U x hxU zU) =
        TopCat.Presheaf.germ (C := AddCommGrpCat)
          (positiveModulePresheaf 𝒜 (m + d)).presheaf U x hxU
            ((positiveMulHomogeneous 𝒜 s m).val.app (op U) zU) := by
    exact hmap.trans (congr_arg
      (fun q ↦ TopCat.Presheaf.germ (C := AddCommGrpCat)
        (positiveModulePresheaf 𝒜 (m + d)).presheaf U x hxU q) happ)
  calc
    _ = positiveStalkToFractionModule 𝒜 (m + d) x
        (TopCat.Presheaf.germ (C := AddCommGrpCat)
          (positiveModulePresheaf 𝒜 (m + d)).presheaf U x hxU
            ((positiveMulHomogeneous 𝒜 s m).val.app (op U) zU)) :=
      congr_arg (positiveStalkToFractionModule 𝒜 (m + d) x) hmap'
    _ = positiveSectionValue 𝒜 (m + d) (op U)
        ((positiveMulHomogeneous 𝒜 s m).val.app (op U) zU) ⟨x, hxU⟩ :=
      positiveStalkToFractionModule_germ 𝒜 (m + d) U x hxU _
    _ = positiveMulHomogeneousStalk 𝒜 (positivePointIdeal 𝒜 x) s m
        (positiveSectionValue 𝒜 m (op U) zU ⟨x, hxU⟩) :=
      positiveSectionValue_mulHomogeneous 𝒜 s m (op U) zU ⟨x, hxU⟩
    _ = positiveMulHomogeneousStalk 𝒜 (positivePointIdeal 𝒜 x) s m
        (positiveStalkToFractionModule 𝒜 m x
          (TopCat.Presheaf.germ (C := AddCommGrpCat)
            (positiveModulePresheaf 𝒜 m).presheaf U x hxU zU)) :=
      congr_arg (positiveMulHomogeneousStalk 𝒜 (positivePointIdeal 𝒜 x) s m)
        (positiveStalkToFractionModule_germ 𝒜 m U x hxU zU).symm

/-- Away from the hypersurface of `s`, positive homogeneous multiplication
is an isomorphism on actual categorical stalks. -/
theorem positiveMulHomogeneous_stalkMap_bijective_of_mem_primeCompl
    {d : ℕ} (s : 𝒜 d) (m : ℕ) (x : X)
    (hs : (s : A) ∈ (positivePointIdeal 𝒜 x).primeCompl)
    (f : 𝒜 1) (hf : (f : A) ∈ (positivePointIdeal 𝒜 x).primeCompl) :
    Function.Bijective
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        (positiveMulHomogeneousPresheaf 𝒜 s m)) := by
  have hsource := positiveStalkToFractionModule_injective 𝒜 m x
  have htarget := positiveStalkToFractionModule_injective 𝒜 (m + d) x
  have hsourceSurj := positiveStalkToFractionModule_surjective 𝒜 m x
  have hconcrete := positiveMulHomogeneousStalk_bijective_of_mem_primeCompl
    𝒜 (positivePointIdeal 𝒜 x) s hs f hf m
  constructor
  · intro z w hzw
    apply hsource
    apply hconcrete.1
    calc
      positiveMulHomogeneousStalk 𝒜 (positivePointIdeal 𝒜 x) s m
          (positiveStalkToFractionModule 𝒜 m x z) =
        positiveStalkToFractionModule 𝒜 (m + d) x
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
            (positiveMulHomogeneousPresheaf 𝒜 s m) z) :=
        (positiveStalkToFractionModule_stalkMap 𝒜 s m x z).symm
      _ = positiveStalkToFractionModule 𝒜 (m + d) x
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
            (positiveMulHomogeneousPresheaf 𝒜 s m) w) := congr_arg _ hzw
      _ = positiveMulHomogeneousStalk 𝒜 (positivePointIdeal 𝒜 x) s m
          (positiveStalkToFractionModule 𝒜 m x w) :=
        positiveStalkToFractionModule_stalkMap 𝒜 s m x w
  · intro z
    obtain ⟨a, ha⟩ := hconcrete.2
      (positiveStalkToFractionModule 𝒜 (m + d) x z)
    obtain ⟨w, hw⟩ := hsourceSurj a
    refine ⟨w, htarget ?_⟩
    calc
      positiveStalkToFractionModule 𝒜 (m + d) x
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
            (positiveMulHomogeneousPresheaf 𝒜 s m) w) =
        positiveMulHomogeneousStalk 𝒜 (positivePointIdeal 𝒜 x) s m
          (positiveStalkToFractionModule 𝒜 m x w) :=
        positiveStalkToFractionModule_stalkMap 𝒜 s m x w
      _ = positiveMulHomogeneousStalk 𝒜 (positivePointIdeal 𝒜 x) s m a :=
        congr_arg _ hw
      _ = positiveStalkToFractionModule 𝒜 (m + d) x z := ha

/-- Categorical form of positive local invertibility. -/
theorem positiveMulHomogeneous_stalkMap_isIso_of_mem_primeCompl
    {d : ℕ} (s : 𝒜 d) (m : ℕ) (x : X)
    (hs : (s : A) ∈ (positivePointIdeal 𝒜 x).primeCompl)
    (f : 𝒜 1) (hf : (f : A) ∈ (positivePointIdeal 𝒜 x).primeCompl) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      (positiveMulHomogeneousPresheaf 𝒜 s m)) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr
    (positiveMulHomogeneous_stalkMap_bijective_of_mem_primeCompl
      𝒜 s m x hs f hf)

/-- Degree-one generation of the irrelevant ideal removes the chart choice
from positive local invertibility. -/
theorem positiveMulHomogeneous_stalkMap_isIso_of_mem_primeCompl_of_irrelevant_le_span
    {d : ℕ} (s : 𝒜 d) (m : ℕ) (x : X)
    (hs : (s : A) ∈ (positivePointIdeal 𝒜 x).primeCompl)
    (hspan : (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤
      Ideal.span (Set.range (fun f : 𝒜 1 => (f : A)))) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      (positiveMulHomogeneousPresheaf 𝒜 s m)) := by
  obtain ⟨f, hf⟩ :=
    exists_degreeOne_mem_primeCompl_of_irrelevant_le_span 𝒜 hspan x
  exact positiveMulHomogeneous_stalkMap_isIso_of_mem_primeCompl
    𝒜 s m x hs f hf

end PositiveSheaf
end ProjectiveNegativeTwist
end PfaffianDescent
