import PacketAssignment
namespace Packet6313
open PacketCoverage
set_option maxRecDepth 500000
set_option maxHeartbeats 0
def multiples (b count : Nat) := (List.range count).map (fun i => b*(i+1))
def stage0 : List Nat := [2, 2]
def stage1 : List Nat := [4, 4]
def stage2 : List Nat := [8, 8]
def stage3 : List Nat := [16, 16]
def stage4 : List Nat := [32, 32]
def stage5 : List Nat := [64, 64]
def stage6 : List Nat := [128, 128]
def stage7 : List Nat := [256, 256]
def stage8 : List Nat := [512, 512]
def stage9 : List Nat := [1024, 1024]
def stage10 : List Nat := [2048, 2048]
def stage11 : List Nat := [4096, 4096]
def stage12 : List Nat := [8192, 8192]
def stage13 : List Nat := [16384, 16384]
def stage14 : List Nat := [384, 3, 49152]
def stage15 : List Nat := [1152, 9, 18]
def stage16 : List Nat := [3456, 27, 54]
def stage17 : List Nat := [10368, 81, 162]
def stage18 : List Nat := [31104, 243, 486]
def stage19 : List Nat := [93312, 729, 1458]
def stage20 : List Nat := [279936, 2187, 4374]
def stage21 : List Nat := [839808, 6561, 13122]
def stage22 : List Nat := [155520, 5, 10, 15, 32805]
def stage23 : List Nat := [777600, 25, 50, 75, 100]
def stage24 : List Nat := [3888000, 125, 250, 375, 500]
def stage25 : List Nat := [299376000, 77, 154, 231, 308, 385, 462, 616, 693, 770, 924, 1155, 1232, 1386, 1540, 1848, 1925, 2079, 2310, 2464, 2772, 3080, 3465, 3696, 3850, 4158, 4620, 4928, 5544, 5775, 6160, 6237, 6930, 7392, 7700, 8316, 9240, 9625, 9856, 10395, 11088, 11550, 12320, 12474, 13860, 14784, 15400, 16632, 17325, 18480, 18711, 19250, 20790, 22176, 23100, 24640, 24948, 27720, 28875, 29568, 30800, 31185, 33264, 34650, 36960, 37422, 38500, 41580, 44352, 46200, 49280, 49896, 51975, 55440, 57750, 61600, 62370]
def stage26 : List Nat := 2095632000 :: (multiples 49 6 ++ [])
def stage27 : List Nat := 23051952000 :: (multiples 121 10 ++ [])
def stage28 : List Nat := 299675376000 :: (multiples 13 12 ++ [])
def stage29 : List Nat := 3895779888000 :: (multiples 169 12 ++ [])
def stage30 : List Nat := 50645138544000 :: (multiples 2197 12 ++ [])
def stage31 : List Nat := 66228258096000 :: (multiples 17 15 ++ [37349])
def stage32 : List Nat := 1125880387632000 :: (multiples 289 16 ++ [])
def stage33 : List Nat := 1258336903824000 :: (multiples 19 17 ++ [5491])
def stage34 : List Nat := 23908401172656000 :: (multiples 361 18 ++ [])
def stage35 : List Nat := 28941748787952000 :: (multiples 23 21 ++ [8303])
def stage36 : List Nat := 665660222122896000 :: (multiples 529 22 ++ [])
def stage37 : List Nat := 839310714850608000 :: (multiples 29 27 ++ [15341])
def stage38 : List Nat := 24340010730667632000 :: (multiples 841 28 ++ [])
def stage39 : List Nat := 26018632160368848000 :: (multiples 31 29 ++ [26071])
def stage40 : List Nat := 806577596971434288000 :: (multiples 961 30 ++ [])
def stage41 : List Nat := 962689389933647376000 :: (multiples 37 35 ++ [35557])
def stage42 : List Nat := 35619507427544952912000 :: (multiples 1369 36 ++ [])
def stage43 : List Nat := 39470264987279542416000 :: (multiples 41 39 ++ [56129])
def stage44 : List Nat := 1697221394453020323888000 :: (multiples 43 42 ++ [])
def stage45 : List Nat := 79769405539291955222736000 :: (multiples 47 46 ++ [])
def stage46 : List Nat := 4227778493582473626805008000 :: (multiples 53 52 ++ [])
def stage47 : List Nat := 249438931121365943981495472000 :: (multiples 59 58 ++ [])
def stage48 : List Nat := 15215774798403322582871223792000 :: (multiples 61 60 ++ [])
def stage49 : List Nat := 1019456911493022613052371994064000 :: (multiples 67 66 ++ [])
def stage50 : List Nat := 72381440716004605526718411578544000 :: (multiples 71 70 ++ [])
def stage51 : List Nat := 5283845172268336203450444045233712000 :: (multiples 73 72 ++ [])
def stage52 : List Nat := 417423768609198560072585079573463248000 :: (multiples 79 78 ++ [])
def stage53 : List Nat := 34646172794563480486024561604597449584000 :: (multiples 83 82 ++ [])
def stage54 : List Nat := 3083509378716149763256185982809173012976000 :: (multiples 89 88 ++ [])
def stage55 : List Nat := 299100409735466527035850040332489782258672000 :: (multiples 97 96 ++ [])
def stage56 : List Nat := 30209141383282119230620854073581468008125872000 :: (multiples 101 100 ++ [])
def stage57 : List Nat := 3111541562478058280753947969578891204836964816000 :: (multiples 103 102 ++ [])
def stage58 : List Nat := 332934947185152236040672432744941358917555235312000 :: (multiples 107 106 ++ [])
def stage59 : List Nat := 36289909243181593728433295169198608122013520649008000 :: (multiples 109 108 ++ [])
def stage60 : List Nat := 4100759744479520091312962354119442717787527833337904000 :: (multiples 113 112 ++ [])
def stage61 : List Nat := 520796487548899051596746218973169225159016034833913808000 :: (multiples 127 126 ++ [])
def stage62 : List Nat := 68224339868905775759173754685485168495831100563242708848000 :: (multiples 131 130 ++ [])
def stage63 : List Nat := 9346734562040091279006804391911468083928860777164251112176000 :: (multiples 137 136 ++ [])
def stage64 : List Nat := 1299196104123572687781945810475694063666111648025830904592464000 :: (multiples 139 138 ++ [])
def stage65 : List Nat := 193580219514412330479509925760878415486250635555848804784277136000 :: (multiples 149 148 ++ [])
def stage66 : List Nat := 29230613146676261902405998789892640738423845968933169522425847536000 :: (multiples 151 150 ++ [])
def stage67 : List Nat := 4589206264028173118677741810013144595932543817122507615020858063152000 :: (multiples 157 156 ++ [])
def stage68 : List Nat := 748040621036592218344471915032142569137004642190968741248399864293776000 :: (multiples 163 162 ++ [])
def stage69 : List Nat := 124922783713110900463526809810367809045879775245891779788482777337060592000 :: (multiples 167 166 ++ [])
def stage70 : List Nat := 21611641582368185780190138097193630964937201117539277903407520479311482416000 :: (multiples 173 172 ++ [])
def stage71 : List Nat := 3868483843243905254654034719397659942723759000039530744709946165796755352464000 :: (multiples 179 178 ++ [])
def stage72 : List Nat := 700195575627146851092380284210976449633000379007155064792500256009212718795984000 :: (multiples 181 180 ++ [])
def stage73 : List Nat := 133737354944785048558644634284296501879903072390366617375367548897759629290032944000 :: (multiples 191 190 ++ [])
def stage74 : List Nat := 25811309504343514371818414416869224862821292971340757153445936937267608452976358192000 :: (multiples 193 192 ++ [])
def stage75 : List Nat := 5084827972355672331248227640123237297975794715354129159228849576641718865236342563824000 :: (multiples 197 196 ++ [])
def stage76 : List Nat := 1011880766498778793918397300384524222297183148355471702686541065751702054182032170200976000 :: (multiples 199 198 ++ [])
def stage77 : List Nat := 213506841731242325516781830381134610904705644303004529266860164873609133432408787912405936000 :: (multiples 211 210 ++ [])
def stage78 : List Nat := 47612025706067038590242348174993018231749358679570010026509816766814836755427159704466523728000 :: (multiples 223 222 ++ [])
def stage79 : List Nat := 10807929835277217759985013035723415138607104420262392276017728406066967943481965252913900886256000 :: (multiples 227 226 ++ [])
def stage80 : List Nat := 2475015932278482867036567985180662066741026912240087831208059804989335659057370042917283302952624000 :: (multiples 229 228 ++ [])
def stage81 : List Nat := 576678712220886508019520340547094261550659270551940464671477934562515208560367219999727009587961392000 :: (multiples 233 232 ++ [])
def stage82 : List Nat := 137826212220791875416665361390755528510607565661913771056483226360441134845927765579934755291522772688000 :: (multiples 239 238 ++ [])
def stage83 : List Nat := 33216117145210841975416352095172082371056423324521218824612457552866313497868591504764276025256988217808000 :: (multiples 241 240 ++ [])
def stage84 : List Nat := (multiples 251 250 ++ [63252])
def packets := [stage0, stage1, stage2, stage3, stage4, stage5, stage6, stage7, stage8, stage9, stage10, stage11, stage12, stage13, stage14, stage15, stage16, stage17, stage18, stage19, stage20, stage21, stage22, stage23, stage24, stage25, stage26, stage27, stage28, stage29, stage30, stage31, stage32, stage33, stage34, stage35, stage36, stage37, stage38, stage39, stage40, stage41, stage42, stage43, stage44, stage45, stage46, stage47, stage48, stage49, stage50, stage51, stage52, stage53, stage54, stage55, stage56, stage57, stage58, stage59, stage60, stage61, stage62, stage63, stage64, stage65, stage66, stage67, stage68, stage69, stage70, stage71, stage72, stage73, stage74, stage75, stage76, stage77, stage78, stage79, stage80, stage81, stage82, stage83, stage84]
theorem valid : Valid 1 packets = true := by decide +kernel
theorem every_integer (x : Int) : Hit 1 packets x := coverage valid (Int.one_dvd x)
def entries := PacketEssential.Flat 1 packets
theorem size : entries.length = 6313 := by decide +kernel
theorem maximum : entries.max? = some 63252 := by decide +kernel
theorem distinct : entries.Nodup := (unused_sound (seen := 0) (by decide +kernel)).1
def trialPrime (p : Nat) : Bool := p ≥ 2 && (List.range (p-2)).all (fun i => p % (i+2) != 0)
def budget (cap : Nat) := 1 + ((List.range 258).filter trialPrime).foldl (fun s p =>
  s + ((List.range 17).filter (fun j => p^(j+1)*(p+1) ≤ cap)).length*(p-1)) 0
theorem budgets : budget 63252 = 6283 ∧ budget 66305 = 6283 ∧ budget 66306 = 6539 := by decide +kernel
theorem fibre_certificate : PacketEssential.StrictValid 1 1 packets = true := by decide +kernel
theorem all_reassignments (f : Nat → Option Int) (h : ∀ x, PacketEssential.Outside entries f x) :
    ∀ n ∈ entries, f n ≠ none := PacketEssential.essential fibre_certificate f h
theorem after_deletion (n : Nat) (hn : n ∈ entries) (a : Nat → Int) :
    ∃ x : Int, ∀ m ∈ entries, m ≠ n → ¬ (m : Int) ∣ x - a m := by
  classical
  apply Classical.byContradiction
  intro h
  let f := fun m => if m=n then none else some (a m)
  have cover (x : Int) : PacketEssential.Outside entries f x := by
    apply Classical.byContradiction
    intro missing
    apply h ⟨x,?_⟩
    intro m hm he hd
    exact missing ⟨m,hm,a m,by simp [f,he],hd⟩
  exact all_reassignments f cover n hn (by simp [f])
theorem covering : ∃ a : Nat → Int, ∀ x : Int, ∃ n ∈ entries, (n : Int) ∣ x-a n :=
  PacketAssignment.covers valid distinct
theorem nontrivial : ∀ n ∈ entries, 1 < n := by
  have h : entries.all (fun n => 1 < n) = true := by decide +kernel
  exact fun n hn => of_decide_eq_true (List.all_eq_true.mp h n hn)
#print axioms covering
#print axioms nontrivial
#print axioms after_deletion
#print axioms every_integer
#print axioms size
#print axioms maximum
#print axioms distinct
#print axioms budgets
end Packet6313
