# FDBLean Claim Status

## Purpose

This document records the epistemic status of the principal claims in
FDBLean. It distinguishes:

- machine-checked theorems;
- explicit definitions and conventions;
- empirical biological inputs;
- formal consequences conditional on those inputs;
- open mathematical and biological questions.

## Machine-checked formal results

### Nucleotide geometry

- The RNA nucleotide alphabet has four elements.
- The three involutions form a Klein four-group action.
- The action is free and transitive.
- The nucleotide alphabet is a Klein torsor.
- The three relative profiles satisfy the XOR law.
- Any two profiles determine the nucleotide.

### Codon geometry

- RNA codon space has 64 elements.
- Codon profile space has 8 elements.
- The three profile partitions are pairwise transverse.
- The resulting structure is a 3-net of order 8.
- The homogeneous union has 22 codons.
- The generic complement has 42 codons.
- The pairwise homogeneous intersections are the origin codon.

### Recoding dynamics

- Directed recoding is:
  - A → G
  - C → U
  - G → G
  - U → U
- Recoding is idempotent.
- Under admissible editing:
  - R is invariant.
  - M changes monotonically according to `M' = M OR E`.
  - S changes according to `S' = S XOR E`.
- The edit mask is recovered exactly from the pre/post S-profile difference.
- The absorbing alphabet is exactly `{G,U}`.
- The absorbing codons are exactly `{G,U}^3`.
- The zero-M origin narrows exactly to `G` or `U`.
- Watson-Crick complementation transports to wobble pairing after recoding.

### RNA/DNA transport

- The map `U ↔ T` defines a bijection between RNA and DNA alphabets.
- The transport preserves all three involutions.
- RNA and DNA codon spaces are equivalent.
- The tagged RNA/DNA nucleotide space has 8 states.
- The tagged construction is only a direct product with polymer identity.
- No relation to 84 or 168 is claimed.

### Pair classification and error geometry

- The six unordered distinct DNA-base pairs partition into:
  - two complement pairs;
  - two wobble-class pairs;
  - two transition pairs.
- Complement and wobble classes reverse ring class.
- Transition class preserves ring class.
- Every mismatch lies in exactly one ring-behavior stratum.

### Genetic code and charge

- The standard RNA genetic code is encoded explicitly.
- There are 61 amino-acid codons and 3 stop codons.
- The amino-acid charge convention is encoded exactly.
- Under A→G editing:
  - position 1 gives `Δq ≤ 0`;
  - position 2 gives `Δq ≥ 0`;
  - position 3 gives `Δq = 0`.

## Declared inputs and conventions

The following are not derived from the Klein geometry:

- the biological interpretation of the three involutions;
- the standard genetic code;
- the amino-acid charge convention;
- histidine charge `+1/2`;
- the biological admissibility of selected editing sites;
- polymerase rejection, repair, or tolerance behavior.

Lean verifies consequences of these declarations once encoded.

## Empirical hypotheses represented but not proved

- specific polymerase mismatch behavior;
- mismatch-repair preferences;
- biochemical tolerance of transition-class mismatches;
- organism-specific editing frequencies;
- selective enrichment of particular codon classes;
- functional or therapeutic utility of derived candidates.

## Open formal questions

- generalization beyond the four-base nucleotide alphabet;
- generalization to nonstandard genetic codes;
- formal treatment of context-dependent editing efficiency;
- integration with protein structure and function;
- formalization of multi-codon and transcript-level constraints;
- stronger abstraction of admissible transport and provenance;
- extension from finite enumeration to scalable biological search.

## Trust and proof status

- No theorem in the main development uses `sorry`.
- No theorem uses `native_decide`.
- Ordinary `decide` is used only for kernel-reducible finite propositions.
- The main theorem chain is assembled in `FDBLean/MainTheoremChain.lean`.
- `#print axioms` results are recorded in `FDBLean/AxiomAudit.lean`.

## What FDBLean does not establish

FDBLean does not by itself establish:

- that the formal structures are uniquely biologically privileged;
- that the framework generalizes to all of biology;
- that the empirical hypotheses are true;
- that the framework improves drug discovery;
- that the framework predicts new therapeutic compounds;
- that the formal model is sufficient for autonomous biological science.

Those are separate scientific questions.


## 1. Foundational nucleotide alphabet

### `Base.lean`
- Four RNA nucleotide states
- Finite cardinality
- Decidable equality and enumeration

### `Involutions.lean`
- Watson–Crick complementation
- Transition substitution
- Wobble pairing
- Fixed-point freedom
- Involutivity
- Pairwise commutation
- Closure under composition

## 2. Klein torsor structure

### `KleinAction.lean`
- Explicit Klein four-group
- Associativity and commutativity
- Self-inverse elements
- Group action on RNA bases
- Freeness
- Transitivity
- Unique transporter
- Nucleotide alphabet as a Klein torsor
- Biochemical composition law

## 3. Binary profile geometry

### `Profiles.lean`
- `R`, `S`, and `M` profiles
- XOR law
- Transformation behavior under the three involutions
- Any two profiles determine the nucleotide
- Relative profiles for arbitrary origin
- Origin-independent XOR law

## 4. Codon space

### `Codon.lean`
- 64-element RNA codon space
- 8-element profile space
- Coordinatewise profiles
- Pointwise XOR law
- Any two codon profiles determine the codon
- Coordinatewise biochemical actions

## 5. Three-net structure

### `ThreeNet.lean`
- Reconstruction from profile pairs
- Unique `R/S` intersections
- Unique `R/M` intersections
- Unique `S/M` intersections
- Pairwise transversality
- Codon 3-net of order 8

## 6. Homogeneous and generic codons

### `HomogeneousSplit.lean`
- Three 8-element homogeneous classes
- Singleton pairwise intersections
- Singleton triple intersection
- 22-element homogeneous union
- 42-element generic complement
- Exhaustive and disjoint `22 + 42 = 64` split

## 7. Directed RNA recoding

### `Recoding.lean`
- Directed substitutions `A → G` and `C → U`
- Editable source predicate
- Idempotence
- Absorbing outputs `G` and `U`
- Codon-level edit masks
- Admissible editing

### `EditingTrichotomy.lean`
- `R′ = R`
- `M′ = M ∨ E`
- `S′ = S ⊕ E`
- Monotonicity of `M`
- Exact recovery of the edit mask from `S`

## 8. Absorbing alphabet and origin narrowing

### `OriginNarrowing.lean`
- Absorbing bases exactly `{G,U}`
- Absorbing codons exactly `{G,U}³`
- Full recoding produces an absorbing codon
- Zero-`M` fiber for origins `G` and `U`
- Admissible origins narrow exactly to `G` or `U`
- Surviving origins form a wobble pair

## 9. Complement-to-wobble transport

### `ComplementToWobble.lean`
- Base-level transport:
  `recodeBase ∘ τc = τw ∘ recodeBase`
- Codon-level transport
- Full recoding maps complementary pairs to wobble pairs
- Fully recoded codons lie in the absorbing set

## 10. DNA alphabet and RNA/DNA transport

### `DNAAlphabet.lean`
- Four-state DNA alphabet
- DNA complement, transition, and third involution
- Involutivity
- Commutation
- Klein closure

### `RNADNATransport.lean`
- Canonical `U ↔ T` equivalence
- RNA/DNA bijection
- Preservation of all three involutions
- RNA/DNA codon equivalence
- Preservation of complete finite geometry

### `TaggedNucleotide.lean`
- RNA/DNA polymer tag
- Eight-state tagged nucleotide space
- Lifted involutions
- Polymer-tag exchange
- Commutation with nucleotide operations
- Explicit quarantine from unrelated `84` or `168` structures

## 11. Pair classification

### `PairClassification.lean`
- Six unordered distinct DNA-base pairs
- Two complement pairs
- Two wobble-class pairs
- Two transition pairs
- Pairwise-disjoint exhaustive partition
- Classification symmetry and uniqueness
- Ring-class preservation or reversal

## 12. Error-control interface

### `ErrorControl.lean`
- Formal mismatch predicate
- Ring-preserving mismatches
- Ring-reversing mismatches
- Transition class exactly ring preserving
- Complement and wobble classes exactly ring reversing
- Exhaustive and disjoint mismatch stratification
- Abstract empirical rejection, repair, and tolerance policy
- Conditional consequences under explicit empirical hypotheses

## 13. Amino-acid and genetic-code layer

### `AminoAcid.lean`
- Twenty standard amino acids
- One-letter and three-letter identifiers
- Injectivity of identifiers

### `StandardCode.lean`
- Full 64-codon standard RNA code
- Explicit stop signal
- Three stop codons
- Sixty-one amino-acid codons
- Exhaustive and exclusive translation classification

## 14. Charge convention

### `Charge.lean`
- Rational amino-acid charge convention
- Histidine assigned `+1/2`
- Positive, negative, and neutral residue classes
- Charge-change function
- Reversal and additive-composition laws
- Optional charge for translation products

## 15. Positional charge theorem

### `PositionalChargeLaw.lean`
- Single-position `A → G` edit
- Integer half-charge representation
- Exact bridge to rational charge
- First-position law: `Δq ≤ 0`
- Second-position law: `Δq ≥ 0`
- Third-position law: `Δq = 0`
- Complete positional charge theorem

## 16. Capstone theorem object

### `MainTheoremChain.lean`
- One typed object collecting the principal theorem chain
- Preserves the distinction among:
  - formal geometry
  - recoding dynamics
  - transported structure
  - empirical interfaces
  - genetic-code consequences

## 17. Trust audit

### `AxiomAudit.lean`
- `#print axioms` results
- No `sorry`
- No `native_decide`
- Explicit record of accepted logical dependencies

# The 272 Theorems of FDBLean

The theorems below are ordered by formal dependency rather than
alphabetically. Line numbers refer to the source file at the time this
document was generated.

---

## 1. Foundational RNA Alphabet

### `Base.lean` — 2 theorems

1. `card_base` — L25  
2. `exhaustive` — L29  

---

## 2. RNA Involutions

### `Involutions.lean` — 9 theorems

3. `tauC_involutive` — L49  
4. `tauT_involutive` — L54  
5. `tauW_involutive` — L59  
6. `tauC_fixed_point_free` — L64  
7. `tauT_fixed_point_free` — L69  
8. `tauW_fixed_point_free` — L74  
9. `tauC_tauT_commute` — L79  
10. `tauC_comp_tauT_eq_tauW` — L84  
11. `tauT_comp_tauC_eq_tauW` — L89  

---

## 3. Klein Four-Group and Torsor Structure

### `KleinAction.lean` — 20 theorems

12. `Klein.card` — L69  
13. `Klein.e_mul` — L75  
14. `Klein.mul_e` — L83  
15. `Klein.mul_assoc` — L91  
16. `Klein.mul_comm` — L99  
17. `Klein.self_inverse` — L107  
18. `Klein.mul_left_cancel` — L116  
19. `Klein.c_ne_t` — L126  
20. `Klein.c_ne_w` — L128  
21. `Klein.t_ne_w` — L130  
22. `Klein.c_mul_t` — L135  
23. `kleinAct_identity` — L153  
24. `kleinAct_mul` — L161  
25. `kleinAct_c` — L171  
26. `kleinAct_t` — L178  
27. `kleinAct_w` — L185  
28. `kleinAct_free` — L192  
29. `kleinAct_exists` — L207  
30. `kleinAct_transporter_unique` — L226  
31. `kleinAct_unique` — L249  
32. `kleinAct_transitive` — L263  
33. `nucleotide_alphabet_is_klein_torsor` — L272  
34. `biochemical_composition_from_action` — L281  

---

## 4. Binary Nucleotide Profiles

### `Profiles.lean` — 18 theorems

35. `profile_xor_law` — L70  
36. `profile_total_xor_zero` — L78  
37. `rBit_tauT` — L90  
38. `sBit_tauT` — L98  
39. `mBit_tauT` — L106  
40. `rBit_tauC` — L114  
41. `sBit_tauC` — L122  
42. `mBit_tauC` — L130  
43. `rBit_tauW` — L138  
44. `sBit_tauW` — L146  
45. `mBit_tauW` — L154  
46. `rs_profile_injective` — L166  
47. `rm_profile_injective` — L175  
48. `sm_profile_injective` — L184  
49. `rBitAt_origin` — L218  
50. `sBitAt_origin` — L226  
51. `mBitAt_origin` — L234  
52. `relative_profile_xor_law` — L242  
53. `relative_rs_profile_injective` — L252  

---

## 5. Codon Space and Coordinatewise Actions

### `Codon.lean` — 13 theorems

54. `card_codon` — L27  
55. `card_codonProfile` — L34  
56. `rProfileAt_originCodon` — L80  
57. `sProfileAt_originCodon` — L90  
58. `mProfileAt_originCodon` — L100  
59. `codon_profile_xor_law` — L114  
60. `mProfileAt_eq_xor` — L129  
61. `rs_codon_profile_injective` — L148  
62. `tauCCodon_involutive` — L191  
63. `tauTCodon_involutive` — L200  
64. `tauWCodon_involutive` — L209  
65. `tauCCodon_comp_tauTCodon` — L219  

---

## 6. Codon Reconstruction and Three-Net Structure

### `ThreeNet.lean` — 17 theorems

66. `rBitAt_baseFromRSAt` — L37  
67. `sBitAt_baseFromRSAt` — L46  
68. `baseFromRSAt_profiles` — L56  
69. `rProfileAt_codonFromRSAt` — L80  
70. `sProfileAt_codonFromRSAt` — L90  
71. `rs_fibers_unique_intersection` — L100  
72. `relative_rm_profile_injective` — L131  
73. `relative_sm_profile_injective` — L143  
74. `rm_codon_profile_injective` — L155  
75. `sm_codon_profile_injective` — L171  
76. `rProfileAt_codonFromRMAt` — L195  
77. `mProfileAt_codonFromRMAt` — L204  
78. `rm_fibers_unique_intersection` — L234  
79. `sProfileAt_codonFromSMAt` — L265  
80. `mProfileAt_codonFromSMAt` — L274  
81. `sm_fibers_unique_intersection` — L303  
82. `codon_profiles_pairwise_transverse` — L324  

---

## 7. The 22/42 Codon Decomposition

### `HomogeneousSplit.lean` — 18 theorems

83. `originCodon_mem_homogeneousR` — L71  
84. `originCodon_mem_homogeneousS` — L79  
85. `originCodon_mem_homogeneousM` — L87  
86. `homogeneousR_card` — L102  
87. `homogeneousS_card` — L110  
88. `homogeneousM_card` — L118  
89. `homogeneousR_inter_homogeneousS` — L130  
90. `homogeneousR_inter_homogeneousM` — L139  
91. `homogeneousS_inter_homogeneousM` — L148  
92. `homogeneous_triple_intersection` — L157  
93. `homogeneous_pairwise_intersection_card` — L168  
94. `homogeneousUnion_card` — L189  
95. `homogeneous_twenty_two_decomposition` — L198  
96. `genericCodons_card` — L205  
97. `codon_twenty_two_forty_two_split` — L213  
98. `homogeneous_generic_disjoint` — L222  
99. `homogeneous_union_generic` — L232  
100. `mem_genericCodons_iff` — L241  

---

## 8. Directed RNA Recoding

### `Recoding.lean` — 16 theorems

101. `recodeBase_A` — L53  
102. `recodeBase_C` — L58  
103. `recodeBase_G` — L63  
104. `recodeBase_U` — L68  
105. `recodeBase_idempotent` — L75  
106. `recodeBase_ne_A` — L83  
107. `recodeBase_ne_C` — L91  
108. `recodeBase_ne_iff` — L100  
109. `recodeBase_eq_self_iff` — L107  
110. `recodeBase_eq_G_or_U` — L115  
111. `recodeCodon_at_selected` — L143  
112. `recodeCodon_at_unselected` — L154  
113. `admissible_recode_selected_eq_G_or_U` — L178  
114. `admissible_recode_selected_A_eq_G` — L192  
115. `admissible_recode_selected_C_eq_U` — L205  
116. `admissible_recode_selected_ne` — L219  
117. `recodeCodon_idempotent` — L235  
118. `recodeCodon_zero` — L251  

---

## 9. Editing Trichotomy

### `EditingTrichotomy.lean` — 11 theorems

119. `rBit_recodeBase` — L29  
120. `sBit_recodeBase_ne_iff` — L38  
121. `mBit_recodeBase_source_true` — L48  
122. `mBit_recodeBase_monotone` — L59  
123. `mBit_recodeBase_true` — L68  
124. `editing_preserves_R` — L80  
125. `editing_M_exact` — L97  
126. `editing_M_monotone` — L117  
127. `editing_S_exact` — L132  
128. `editing_S_changes_iff` — L153  
129. `editing_mask_recovered_by_S` — L175  
130. `editing_trichotomy` — L193  

---

## 10. Absorbing Alphabet and Origin Narrowing

### `OriginNarrowing.lean` — 15 theorems

131. `absorbingBase_iff` — L33  
132. `absorbingBase_G` — L41  
133. `absorbingBase_U` — L48  
134. `not_absorbingBase_A` — L55  
135. `not_absorbingBase_C` — L62  
136. `absorbingCodon_iff` — L77  
137. `full_recode_is_absorbing` — L91  
138. `absorbingCodon_iff_full_recode_fixed` — L102  
139. `mBitAt_G_zero_iff` — L125  
140. `mBitAt_U_zero_iff` — L133  
141. `mProfileAt_G_zero_iff_absorbing` — L142  
142. `mProfileAt_U_zero_iff_absorbing` — L164  
143. `origin_narrowing` — L186  
144. `tauW_G_eq_U` — L201  
145. `tauW_U_eq_G` — L208  
146. `narrowed_origins_form_wobble_pair` — L216  

---

## 11. Complement-to-Wobble Transport

### `ComplementToWobble.lean` — 9 theorems

147. `recodeBase_tauC_eq_tauW_recodeBase` — L29  
148. `recodeBase_comp_tauC` — L38  
149. `recoded_complement_pair_absorbing` — L48  
150. `recoded_complement_is_wobble_partner` — L60  
151. `fullyRecodeCodon_apply` — L81  
152. `fullyRecodeCodon_tauC` — L92  
153. `fullyRecodeCodon_comp_tauCCodon` — L107  
154. `fullyRecodeCodon_absorbing` — L116  
155. `complement_becomes_wobble` — L125  

---

## 12. DNA Alphabet

### `DNAAlphabet.lean` — 7 theorems

156. `DNABase.tauC_involutive` — L64  
157. `DNABase.tauT_involutive` — L72  
158. `DNABase.tauW_involutive` — L80  
159. `DNABase.tauC_tauT_commute` — L88  
160. `DNABase.tauC_comp_tauT_eq_tauW` — L97  
161. `DNABase.tauT_comp_tauC_eq_tauW` — L106  
162. `DNABase.card` — L114  

---

## 13. RNA/DNA Transport

### `RNADNATransport.lean` — 21 theorems

163. `dnaToRNA_rnaToDNA` — L46  
164. `rnaToDNA_dnaToRNA` — L52  
165. `rnaToDNA_injective` — L69  
166. `rnaToDNA_surjective` — L76  
167. `rnaToDNA_tauC` — L87  
168. `rnaToDNA_tauT` — L96  
169. `rnaToDNA_tauW` — L105  
170. `dnaToRNA_tauC` — L114  
171. `dnaToRNA_tauT` — L123  
172. `dnaToRNA_tauW` — L132  
173. `rnaToDNA_comp_tauC` — L141  
174. `rnaToDNA_comp_tauT` — L150  
175. `rnaToDNA_comp_tauW` — L159  
176. `dnaCodonToRNA_rnaCodonToDNA` — L191  
177. `rnaCodonToDNA_dnaCodonToRNA` — L198  
178. `card_dnaCodon` — L216  
179. `card_rnaCodon_eq_card_dnaCodon` — L223  
180. `rnaCodonToDNA_tauC` — L232  
181. `rnaCodonToDNA_tauT` — L244  
182. `rnaCodonToDNA_tauW` — L256  
183. `rna_dna_geometry_preserved` — L268  

---

## 14. Tagged RNA/DNA Nucleotide Space

### `TaggedNucleotide.lean` — 18 theorems

184. `PolymerTag.flip_involutive` — L45  
185. `PolymerTag.card` — L53  
186. `card_taggedNucleotide` — L75  
187. `taggedAsRNA_tagRNA` — L113  
188. `taggedAsDNA_tagDNA` — L119  
189. `tagRNA_injective` — L127  
190. `tagDNA_injective` — L135  
191. `tagRNA_ne_tagDNA` — L144  
192. `taggedTauC_involutive` — L196  
193. `taggedTauT_involutive` — L206  
194. `taggedTauW_involutive` — L216  
195. `taggedPolymerFlip_involutive` — L226  
196. `taggedTauC_preserves_tag` — L237  
197. `taggedTauT_preserves_tag` — L242  
198. `taggedTauW_preserves_tag` — L247  
199. `taggedPolymerFlip_commutes_tauC` — L255  
200. `taggedPolymerFlip_commutes_tauT` — L265  
201. `taggedPolymerFlip_commutes_tauW` — L275  
202. `tagged_nucleotide_is_eight_state_product` — L286  

---

## 15. DNA Pair Classification

### `PairClassification.lean` — 20 theorems

203. `classifyPair_eq_none_iff` — L70  
204. `classifyPair_eq_complement_iff` — L80  
205. `classifyPair_eq_wobble_iff` — L91  
206. `classifyPair_eq_transition_iff` — L102  
207. `classifyPair_symmetric` — L112  
208. `distinct_pair_classified` — L122  
209. `distinct_pair_class_unique` — L133  
210. `complementPairSet_card` — L194  
211. `wobblePairSet_card` — L201  
212. `transitionPairSet_card` — L208  
213. `pair_sets_pairwise_disjoint` — L215  
214. `allDistinctPairSet_card` — L224  
215. `allDistinctPairSet_complete` — L232  
216. `mismatch_classification` — L243  
217. `dnaRBit_tauC` — L276  
218. `dnaRBit_tauW` — L285  
219. `dnaRBit_tauT` — L294  
220. `complement_pair_inverts_ring_class` — L303  
221. `wobble_pair_inverts_ring_class` — L318  
222. `transition_pair_preserves_ring_class` — L333  
223. `pair_classification_with_ring_behavior` — L348  

---

## 16. Error-Control Geometry and Empirical Interface

### `ErrorControl.lean` — 14 theorems

224. `transition_pair_is_mismatch` — L82  
225. `complement_pair_is_mismatch` — L99  
226. `wobble_pair_is_mismatch` — L116  
227. `transition_pair_ring_preserving` — L133  
228. `complement_pair_ring_reversing` — L147  
229. `wobble_pair_ring_reversing` — L160  
230. `ring_preserving_iff_transition` — L174  
231. `ring_reversing_iff_complement_or_wobble` — L186  
232. `mismatch_ring_modes_disjoint` — L199  
233. `mismatch_ring_modes_exhaustive` — L211  
234. `complement_controlled_of_ring_reversing` — L294  
235. `wobble_controlled_of_ring_reversing` — L309  
236. `transition_tolerated_of_ring_preserving` — L324  
237. `formal_error_control_stratification` — L340  

---

## 17. Amino-Acid Alphabet

### `AminoAcid.lean` — 3 theorems

238. `AminoAcid.card` — L47  
239. `AminoAcid.abbreviation_injective` — L106  
240. `AminoAcid.oneLetter_injective` — L115  

---

## 18. Standard Genetic Code

### `StandardCode.lean` — 5 theorems

241. `standardCode_eq_stop_iff` — L135  
242. `standard_stop_codon_count` — L146  
243. `standard_amino_acid_codon_count` — L155  
244. `standardCode_exhaustive` — L165  
245. `aminoAcid_ne_stop` — L179  

---

## 19. Amino-Acid Charge Convention

### `Charge.lean` — 13 theorems

246. `charge_Arg` — L53  
247. `charge_Lys` — L58  
248. `charge_His` — L63  
249. `charge_Asp` — L68  
250. `charge_Glu` — L73  
251. `aminoAcidCharge_range` — L81  
252. `aminoAcidCharge_pos_iff` — L93  
253. `aminoAcidCharge_neg_iff` — L103  
254. `aminoAcidCharge_eq_zero_iff` — L113  
255. `chargeChange_self` — L138  
256. `chargeChange_reverse` — L146  
257. `chargeChange_add` — L156  
258. `translationProductCharge_aminoAcid` — L175  
259. `translationProductCharge_stop` — L183  

---

## 20. Positional Charge Law

### `PositionalChargeLaw.lean` — 11 theorems

260. `editAAt_same` — L50  
261. `editAAt_other` — L56  
262. `editAAt_idempotent` — L66  
263. `aminoAcidCharge_eq_chargeUnits_half` — L116  
264. `chargeChange_eq_chargeUnitChange_half` — L134  
265. `first_position_charge_units_nonpositive` — L154  
266. `second_position_charge_units_nonnegative` — L170  
267. `third_position_charge_units_zero` — L186  
268. `first_position_charge_nonpositive` — L205  
269. `second_position_charge_nonnegative` — L232  
270. `third_position_charge_zero` — L260  
271. `positional_charge_law` — L287  

---

## 21. Capstone Theorem Chain

### `MainTheoremChain.lean` — 1 theorem

272. `mainTheoremChain` — L190  

---

## Summary

| Formal layer | Theorems |
|---|---:|
| Foundational alphabet and involutions | 11 |
| Klein torsor | 23 |
| Profiles and codon geometry | 48 |
| 22/42 decomposition | 18 |
| Recoding, trichotomy, and narrowing | 46 |
| RNA/DNA transport and tagging | 55 |
| Pair classification and error control | 34 |
| Amino acids, code, and charge | 34 |
| Capstone | 1 |
| **Total** | **272** |