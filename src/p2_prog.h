/*  Poseidon2 over BabyBear, width 16, printed by lean/P2Prog.lean from
 *  the program Lean proves equal to lean-ski's specification
 *  (AvonP2.permuteC).  Generated; do not edit. */

#include <stdint.h>

/*  sboxC: x^7 mod p, each product below 2^62. */
static uint64_t av_p2_sbox(uint64_t x) {
    uint64_t a = x % UINT64_C(2013265921);
    uint64_t a2 = a * a % UINT64_C(2013265921);
    uint64_t a3 = a2 * a % UINT64_C(2013265921);
    uint64_t a6 = a3 * a3 % UINT64_C(2013265921);
    return a6 * a % UINT64_C(2013265921);
}

static void av_p2_layer0(uint32_t s[16]) {
    uint64_t t[16];
    t[0] = (((((UINT64_C(2) * (uint64_t)s[0]) + (UINT64_C(3) * (uint64_t)s[1])) + (uint64_t)s[2]) + (uint64_t)s[3]) % UINT64_C(2013265921));
    t[1] = (((((uint64_t)s[0] + (UINT64_C(2) * (uint64_t)s[1])) + (UINT64_C(3) * (uint64_t)s[2])) + (uint64_t)s[3]) % UINT64_C(2013265921));
    t[2] = (((((uint64_t)s[0] + (uint64_t)s[1]) + (UINT64_C(2) * (uint64_t)s[2])) + (UINT64_C(3) * (uint64_t)s[3])) % UINT64_C(2013265921));
    t[3] = (((((UINT64_C(3) * (uint64_t)s[0]) + (uint64_t)s[1]) + (uint64_t)s[2]) + (UINT64_C(2) * (uint64_t)s[3])) % UINT64_C(2013265921));
    t[4] = (((((UINT64_C(2) * (uint64_t)s[4]) + (UINT64_C(3) * (uint64_t)s[5])) + (uint64_t)s[6]) + (uint64_t)s[7]) % UINT64_C(2013265921));
    t[5] = (((((uint64_t)s[4] + (UINT64_C(2) * (uint64_t)s[5])) + (UINT64_C(3) * (uint64_t)s[6])) + (uint64_t)s[7]) % UINT64_C(2013265921));
    t[6] = (((((uint64_t)s[4] + (uint64_t)s[5]) + (UINT64_C(2) * (uint64_t)s[6])) + (UINT64_C(3) * (uint64_t)s[7])) % UINT64_C(2013265921));
    t[7] = (((((UINT64_C(3) * (uint64_t)s[4]) + (uint64_t)s[5]) + (uint64_t)s[6]) + (UINT64_C(2) * (uint64_t)s[7])) % UINT64_C(2013265921));
    t[8] = (((((UINT64_C(2) * (uint64_t)s[8]) + (UINT64_C(3) * (uint64_t)s[9])) + (uint64_t)s[10]) + (uint64_t)s[11]) % UINT64_C(2013265921));
    t[9] = (((((uint64_t)s[8] + (UINT64_C(2) * (uint64_t)s[9])) + (UINT64_C(3) * (uint64_t)s[10])) + (uint64_t)s[11]) % UINT64_C(2013265921));
    t[10] = (((((uint64_t)s[8] + (uint64_t)s[9]) + (UINT64_C(2) * (uint64_t)s[10])) + (UINT64_C(3) * (uint64_t)s[11])) % UINT64_C(2013265921));
    t[11] = (((((UINT64_C(3) * (uint64_t)s[8]) + (uint64_t)s[9]) + (uint64_t)s[10]) + (UINT64_C(2) * (uint64_t)s[11])) % UINT64_C(2013265921));
    t[12] = (((((UINT64_C(2) * (uint64_t)s[12]) + (UINT64_C(3) * (uint64_t)s[13])) + (uint64_t)s[14]) + (uint64_t)s[15]) % UINT64_C(2013265921));
    t[13] = (((((uint64_t)s[12] + (UINT64_C(2) * (uint64_t)s[13])) + (UINT64_C(3) * (uint64_t)s[14])) + (uint64_t)s[15]) % UINT64_C(2013265921));
    t[14] = (((((uint64_t)s[12] + (uint64_t)s[13]) + (UINT64_C(2) * (uint64_t)s[14])) + (UINT64_C(3) * (uint64_t)s[15])) % UINT64_C(2013265921));
    t[15] = (((((UINT64_C(3) * (uint64_t)s[12]) + (uint64_t)s[13]) + (uint64_t)s[14]) + (UINT64_C(2) * (uint64_t)s[15])) % UINT64_C(2013265921));
    for (int i = 0; i < 16; i++) s[i] = (uint32_t)t[i];
}

static void av_p2_layer1(uint32_t s[16]) {
    uint64_t t[16];
    t[0] = (((uint64_t)s[0] + (((((UINT64_C(0) + (uint64_t)s[0]) + (uint64_t)s[4]) + (uint64_t)s[8]) + (uint64_t)s[12]) % UINT64_C(2013265921))) % UINT64_C(2013265921));
    t[1] = (((uint64_t)s[1] + (((((UINT64_C(0) + (uint64_t)s[1]) + (uint64_t)s[5]) + (uint64_t)s[9]) + (uint64_t)s[13]) % UINT64_C(2013265921))) % UINT64_C(2013265921));
    t[2] = (((uint64_t)s[2] + (((((UINT64_C(0) + (uint64_t)s[2]) + (uint64_t)s[6]) + (uint64_t)s[10]) + (uint64_t)s[14]) % UINT64_C(2013265921))) % UINT64_C(2013265921));
    t[3] = (((uint64_t)s[3] + (((((UINT64_C(0) + (uint64_t)s[3]) + (uint64_t)s[7]) + (uint64_t)s[11]) + (uint64_t)s[15]) % UINT64_C(2013265921))) % UINT64_C(2013265921));
    t[4] = (((uint64_t)s[4] + (((((UINT64_C(0) + (uint64_t)s[0]) + (uint64_t)s[4]) + (uint64_t)s[8]) + (uint64_t)s[12]) % UINT64_C(2013265921))) % UINT64_C(2013265921));
    t[5] = (((uint64_t)s[5] + (((((UINT64_C(0) + (uint64_t)s[1]) + (uint64_t)s[5]) + (uint64_t)s[9]) + (uint64_t)s[13]) % UINT64_C(2013265921))) % UINT64_C(2013265921));
    t[6] = (((uint64_t)s[6] + (((((UINT64_C(0) + (uint64_t)s[2]) + (uint64_t)s[6]) + (uint64_t)s[10]) + (uint64_t)s[14]) % UINT64_C(2013265921))) % UINT64_C(2013265921));
    t[7] = (((uint64_t)s[7] + (((((UINT64_C(0) + (uint64_t)s[3]) + (uint64_t)s[7]) + (uint64_t)s[11]) + (uint64_t)s[15]) % UINT64_C(2013265921))) % UINT64_C(2013265921));
    t[8] = (((uint64_t)s[8] + (((((UINT64_C(0) + (uint64_t)s[0]) + (uint64_t)s[4]) + (uint64_t)s[8]) + (uint64_t)s[12]) % UINT64_C(2013265921))) % UINT64_C(2013265921));
    t[9] = (((uint64_t)s[9] + (((((UINT64_C(0) + (uint64_t)s[1]) + (uint64_t)s[5]) + (uint64_t)s[9]) + (uint64_t)s[13]) % UINT64_C(2013265921))) % UINT64_C(2013265921));
    t[10] = (((uint64_t)s[10] + (((((UINT64_C(0) + (uint64_t)s[2]) + (uint64_t)s[6]) + (uint64_t)s[10]) + (uint64_t)s[14]) % UINT64_C(2013265921))) % UINT64_C(2013265921));
    t[11] = (((uint64_t)s[11] + (((((UINT64_C(0) + (uint64_t)s[3]) + (uint64_t)s[7]) + (uint64_t)s[11]) + (uint64_t)s[15]) % UINT64_C(2013265921))) % UINT64_C(2013265921));
    t[12] = (((uint64_t)s[12] + (((((UINT64_C(0) + (uint64_t)s[0]) + (uint64_t)s[4]) + (uint64_t)s[8]) + (uint64_t)s[12]) % UINT64_C(2013265921))) % UINT64_C(2013265921));
    t[13] = (((uint64_t)s[13] + (((((UINT64_C(0) + (uint64_t)s[1]) + (uint64_t)s[5]) + (uint64_t)s[9]) + (uint64_t)s[13]) % UINT64_C(2013265921))) % UINT64_C(2013265921));
    t[14] = (((uint64_t)s[14] + (((((UINT64_C(0) + (uint64_t)s[2]) + (uint64_t)s[6]) + (uint64_t)s[10]) + (uint64_t)s[14]) % UINT64_C(2013265921))) % UINT64_C(2013265921));
    t[15] = (((uint64_t)s[15] + (((((UINT64_C(0) + (uint64_t)s[3]) + (uint64_t)s[7]) + (uint64_t)s[11]) + (uint64_t)s[15]) % UINT64_C(2013265921))) % UINT64_C(2013265921));
    for (int i = 0; i < 16; i++) s[i] = (uint32_t)t[i];
}

static void av_p2_layer2(uint32_t s[16]) {
    uint64_t t[16];
    t[0] = av_p2_sbox(((uint64_t)s[0] + UINT64_C(1774958255)));
    t[1] = av_p2_sbox(((uint64_t)s[1] + UINT64_C(1185780729)));
    t[2] = av_p2_sbox(((uint64_t)s[2] + UINT64_C(1621102414)));
    t[3] = av_p2_sbox(((uint64_t)s[3] + UINT64_C(1796380621)));
    t[4] = av_p2_sbox(((uint64_t)s[4] + UINT64_C(588815102)));
    t[5] = av_p2_sbox(((uint64_t)s[5] + UINT64_C(1932426223)));
    t[6] = av_p2_sbox(((uint64_t)s[6] + UINT64_C(1925334750)));
    t[7] = av_p2_sbox(((uint64_t)s[7] + UINT64_C(747903232)));
    t[8] = av_p2_sbox(((uint64_t)s[8] + UINT64_C(89648862)));
    t[9] = av_p2_sbox(((uint64_t)s[9] + UINT64_C(360728943)));
    t[10] = av_p2_sbox(((uint64_t)s[10] + UINT64_C(977184635)));
    t[11] = av_p2_sbox(((uint64_t)s[11] + UINT64_C(1425273457)));
    t[12] = av_p2_sbox(((uint64_t)s[12] + UINT64_C(256487465)));
    t[13] = av_p2_sbox(((uint64_t)s[13] + UINT64_C(1200041953)));
    t[14] = av_p2_sbox(((uint64_t)s[14] + UINT64_C(572403254)));
    t[15] = av_p2_sbox(((uint64_t)s[15] + UINT64_C(448208942)));
    for (int i = 0; i < 16; i++) s[i] = (uint32_t)t[i];
}

static void av_p2_layer3(uint32_t s[16]) {
    uint64_t t[16];
    t[0] = av_p2_sbox(((uint64_t)s[0] + UINT64_C(1215789478)));
    t[1] = av_p2_sbox(((uint64_t)s[1] + UINT64_C(944884184)));
    t[2] = av_p2_sbox(((uint64_t)s[2] + UINT64_C(953948096)));
    t[3] = av_p2_sbox(((uint64_t)s[3] + UINT64_C(547326025)));
    t[4] = av_p2_sbox(((uint64_t)s[4] + UINT64_C(646827752)));
    t[5] = av_p2_sbox(((uint64_t)s[5] + UINT64_C(889997530)));
    t[6] = av_p2_sbox(((uint64_t)s[6] + UINT64_C(1536873262)));
    t[7] = av_p2_sbox(((uint64_t)s[7] + UINT64_C(86189867)));
    t[8] = av_p2_sbox(((uint64_t)s[8] + UINT64_C(1065944411)));
    t[9] = av_p2_sbox(((uint64_t)s[9] + UINT64_C(32019634)));
    t[10] = av_p2_sbox(((uint64_t)s[10] + UINT64_C(333311454)));
    t[11] = av_p2_sbox(((uint64_t)s[11] + UINT64_C(456061748)));
    t[12] = av_p2_sbox(((uint64_t)s[12] + UINT64_C(1963448500)));
    t[13] = av_p2_sbox(((uint64_t)s[13] + UINT64_C(1827584334)));
    t[14] = av_p2_sbox(((uint64_t)s[14] + UINT64_C(1391160226)));
    t[15] = av_p2_sbox(((uint64_t)s[15] + UINT64_C(1348741381)));
    for (int i = 0; i < 16; i++) s[i] = (uint32_t)t[i];
}

static void av_p2_layer4(uint32_t s[16]) {
    uint64_t t[16];
    t[0] = av_p2_sbox(((uint64_t)s[0] + UINT64_C(88424255)));
    t[1] = av_p2_sbox(((uint64_t)s[1] + UINT64_C(104111868)));
    t[2] = av_p2_sbox(((uint64_t)s[2] + UINT64_C(1763866748)));
    t[3] = av_p2_sbox(((uint64_t)s[3] + UINT64_C(79691676)));
    t[4] = av_p2_sbox(((uint64_t)s[4] + UINT64_C(1988915530)));
    t[5] = av_p2_sbox(((uint64_t)s[5] + UINT64_C(1050669594)));
    t[6] = av_p2_sbox(((uint64_t)s[6] + UINT64_C(359890076)));
    t[7] = av_p2_sbox(((uint64_t)s[7] + UINT64_C(573163527)));
    t[8] = av_p2_sbox(((uint64_t)s[8] + UINT64_C(222820492)));
    t[9] = av_p2_sbox(((uint64_t)s[9] + UINT64_C(159256268)));
    t[10] = av_p2_sbox(((uint64_t)s[10] + UINT64_C(669703072)));
    t[11] = av_p2_sbox(((uint64_t)s[11] + UINT64_C(763177444)));
    t[12] = av_p2_sbox(((uint64_t)s[12] + UINT64_C(889367200)));
    t[13] = av_p2_sbox(((uint64_t)s[13] + UINT64_C(256335831)));
    t[14] = av_p2_sbox(((uint64_t)s[14] + UINT64_C(704371273)));
    t[15] = av_p2_sbox(((uint64_t)s[15] + UINT64_C(25886717)));
    for (int i = 0; i < 16; i++) s[i] = (uint32_t)t[i];
}

static void av_p2_layer5(uint32_t s[16]) {
    uint64_t t[16];
    t[0] = av_p2_sbox(((uint64_t)s[0] + UINT64_C(51754520)));
    t[1] = av_p2_sbox(((uint64_t)s[1] + UINT64_C(1833211857)));
    t[2] = av_p2_sbox(((uint64_t)s[2] + UINT64_C(454499742)));
    t[3] = av_p2_sbox(((uint64_t)s[3] + UINT64_C(1384520381)));
    t[4] = av_p2_sbox(((uint64_t)s[4] + UINT64_C(777848065)));
    t[5] = av_p2_sbox(((uint64_t)s[5] + UINT64_C(1053320300)));
    t[6] = av_p2_sbox(((uint64_t)s[6] + UINT64_C(1851729162)));
    t[7] = av_p2_sbox(((uint64_t)s[7] + UINT64_C(344647910)));
    t[8] = av_p2_sbox(((uint64_t)s[8] + UINT64_C(401996362)));
    t[9] = av_p2_sbox(((uint64_t)s[9] + UINT64_C(1046925956)));
    t[10] = av_p2_sbox(((uint64_t)s[10] + UINT64_C(5351995)));
    t[11] = av_p2_sbox(((uint64_t)s[11] + UINT64_C(1212119315)));
    t[12] = av_p2_sbox(((uint64_t)s[12] + UINT64_C(754867989)));
    t[13] = av_p2_sbox(((uint64_t)s[13] + UINT64_C(36972490)));
    t[14] = av_p2_sbox(((uint64_t)s[14] + UINT64_C(751272725)));
    t[15] = av_p2_sbox(((uint64_t)s[15] + UINT64_C(506915399)));
    for (int i = 0; i < 16; i++) s[i] = (uint32_t)t[i];
}

static void av_p2_layer6(uint32_t s[16]) {
    uint64_t t[16];
    t[0] = av_p2_sbox(((uint64_t)s[0] + UINT64_C(1518359488)));
    t[1] = (uint64_t)s[1];
    t[2] = (uint64_t)s[2];
    t[3] = (uint64_t)s[3];
    t[4] = (uint64_t)s[4];
    t[5] = (uint64_t)s[5];
    t[6] = (uint64_t)s[6];
    t[7] = (uint64_t)s[7];
    t[8] = (uint64_t)s[8];
    t[9] = (uint64_t)s[9];
    t[10] = (uint64_t)s[10];
    t[11] = (uint64_t)s[11];
    t[12] = (uint64_t)s[12];
    t[13] = (uint64_t)s[13];
    t[14] = (uint64_t)s[14];
    t[15] = (uint64_t)s[15];
    for (int i = 0; i < 16; i++) s[i] = (uint32_t)t[i];
}

static void av_p2_layer7(uint32_t s[16]) {
    uint64_t t[16];
    t[0] = (((((((((((((((((((UINT64_C(0) + (uint64_t)s[0]) + (uint64_t)s[1]) + (uint64_t)s[2]) + (uint64_t)s[3]) + (uint64_t)s[4]) + (uint64_t)s[5]) + (uint64_t)s[6]) + (uint64_t)s[7]) + (uint64_t)s[8]) + (uint64_t)s[9]) + (uint64_t)s[10]) + (uint64_t)s[11]) + (uint64_t)s[12]) + (uint64_t)s[13]) + (uint64_t)s[14]) + (uint64_t)s[15]) % UINT64_C(2013265921)) + (UINT64_C(2013265919) * (uint64_t)s[0])) % UINT64_C(2013265921));
    t[1] = (((((((((((((((((((UINT64_C(0) + (uint64_t)s[0]) + (uint64_t)s[1]) + (uint64_t)s[2]) + (uint64_t)s[3]) + (uint64_t)s[4]) + (uint64_t)s[5]) + (uint64_t)s[6]) + (uint64_t)s[7]) + (uint64_t)s[8]) + (uint64_t)s[9]) + (uint64_t)s[10]) + (uint64_t)s[11]) + (uint64_t)s[12]) + (uint64_t)s[13]) + (uint64_t)s[14]) + (uint64_t)s[15]) % UINT64_C(2013265921)) + (UINT64_C(1) * (uint64_t)s[1])) % UINT64_C(2013265921));
    t[2] = (((((((((((((((((((UINT64_C(0) + (uint64_t)s[0]) + (uint64_t)s[1]) + (uint64_t)s[2]) + (uint64_t)s[3]) + (uint64_t)s[4]) + (uint64_t)s[5]) + (uint64_t)s[6]) + (uint64_t)s[7]) + (uint64_t)s[8]) + (uint64_t)s[9]) + (uint64_t)s[10]) + (uint64_t)s[11]) + (uint64_t)s[12]) + (uint64_t)s[13]) + (uint64_t)s[14]) + (uint64_t)s[15]) % UINT64_C(2013265921)) + (UINT64_C(2) * (uint64_t)s[2])) % UINT64_C(2013265921));
    t[3] = (((((((((((((((((((UINT64_C(0) + (uint64_t)s[0]) + (uint64_t)s[1]) + (uint64_t)s[2]) + (uint64_t)s[3]) + (uint64_t)s[4]) + (uint64_t)s[5]) + (uint64_t)s[6]) + (uint64_t)s[7]) + (uint64_t)s[8]) + (uint64_t)s[9]) + (uint64_t)s[10]) + (uint64_t)s[11]) + (uint64_t)s[12]) + (uint64_t)s[13]) + (uint64_t)s[14]) + (uint64_t)s[15]) % UINT64_C(2013265921)) + (UINT64_C(1006632961) * (uint64_t)s[3])) % UINT64_C(2013265921));
    t[4] = (((((((((((((((((((UINT64_C(0) + (uint64_t)s[0]) + (uint64_t)s[1]) + (uint64_t)s[2]) + (uint64_t)s[3]) + (uint64_t)s[4]) + (uint64_t)s[5]) + (uint64_t)s[6]) + (uint64_t)s[7]) + (uint64_t)s[8]) + (uint64_t)s[9]) + (uint64_t)s[10]) + (uint64_t)s[11]) + (uint64_t)s[12]) + (uint64_t)s[13]) + (uint64_t)s[14]) + (uint64_t)s[15]) % UINT64_C(2013265921)) + (UINT64_C(3) * (uint64_t)s[4])) % UINT64_C(2013265921));
    t[5] = (((((((((((((((((((UINT64_C(0) + (uint64_t)s[0]) + (uint64_t)s[1]) + (uint64_t)s[2]) + (uint64_t)s[3]) + (uint64_t)s[4]) + (uint64_t)s[5]) + (uint64_t)s[6]) + (uint64_t)s[7]) + (uint64_t)s[8]) + (uint64_t)s[9]) + (uint64_t)s[10]) + (uint64_t)s[11]) + (uint64_t)s[12]) + (uint64_t)s[13]) + (uint64_t)s[14]) + (uint64_t)s[15]) % UINT64_C(2013265921)) + (UINT64_C(4) * (uint64_t)s[5])) % UINT64_C(2013265921));
    t[6] = (((((((((((((((((((UINT64_C(0) + (uint64_t)s[0]) + (uint64_t)s[1]) + (uint64_t)s[2]) + (uint64_t)s[3]) + (uint64_t)s[4]) + (uint64_t)s[5]) + (uint64_t)s[6]) + (uint64_t)s[7]) + (uint64_t)s[8]) + (uint64_t)s[9]) + (uint64_t)s[10]) + (uint64_t)s[11]) + (uint64_t)s[12]) + (uint64_t)s[13]) + (uint64_t)s[14]) + (uint64_t)s[15]) % UINT64_C(2013265921)) + (UINT64_C(1006632960) * (uint64_t)s[6])) % UINT64_C(2013265921));
    t[7] = (((((((((((((((((((UINT64_C(0) + (uint64_t)s[0]) + (uint64_t)s[1]) + (uint64_t)s[2]) + (uint64_t)s[3]) + (uint64_t)s[4]) + (uint64_t)s[5]) + (uint64_t)s[6]) + (uint64_t)s[7]) + (uint64_t)s[8]) + (uint64_t)s[9]) + (uint64_t)s[10]) + (uint64_t)s[11]) + (uint64_t)s[12]) + (uint64_t)s[13]) + (uint64_t)s[14]) + (uint64_t)s[15]) % UINT64_C(2013265921)) + (UINT64_C(2013265918) * (uint64_t)s[7])) % UINT64_C(2013265921));
    t[8] = (((((((((((((((((((UINT64_C(0) + (uint64_t)s[0]) + (uint64_t)s[1]) + (uint64_t)s[2]) + (uint64_t)s[3]) + (uint64_t)s[4]) + (uint64_t)s[5]) + (uint64_t)s[6]) + (uint64_t)s[7]) + (uint64_t)s[8]) + (uint64_t)s[9]) + (uint64_t)s[10]) + (uint64_t)s[11]) + (uint64_t)s[12]) + (uint64_t)s[13]) + (uint64_t)s[14]) + (uint64_t)s[15]) % UINT64_C(2013265921)) + (UINT64_C(2013265917) * (uint64_t)s[8])) % UINT64_C(2013265921));
    t[9] = (((((((((((((((((((UINT64_C(0) + (uint64_t)s[0]) + (uint64_t)s[1]) + (uint64_t)s[2]) + (uint64_t)s[3]) + (uint64_t)s[4]) + (uint64_t)s[5]) + (uint64_t)s[6]) + (uint64_t)s[7]) + (uint64_t)s[8]) + (uint64_t)s[9]) + (uint64_t)s[10]) + (uint64_t)s[11]) + (uint64_t)s[12]) + (uint64_t)s[13]) + (uint64_t)s[14]) + (uint64_t)s[15]) % UINT64_C(2013265921)) + (UINT64_C(2005401601) * (uint64_t)s[9])) % UINT64_C(2013265921));
    t[10] = (((((((((((((((((((UINT64_C(0) + (uint64_t)s[0]) + (uint64_t)s[1]) + (uint64_t)s[2]) + (uint64_t)s[3]) + (uint64_t)s[4]) + (uint64_t)s[5]) + (uint64_t)s[6]) + (uint64_t)s[7]) + (uint64_t)s[8]) + (uint64_t)s[9]) + (uint64_t)s[10]) + (uint64_t)s[11]) + (uint64_t)s[12]) + (uint64_t)s[13]) + (uint64_t)s[14]) + (uint64_t)s[15]) % UINT64_C(2013265921)) + (UINT64_C(1509949441) * (uint64_t)s[10])) % UINT64_C(2013265921));
    t[11] = (((((((((((((((((((UINT64_C(0) + (uint64_t)s[0]) + (uint64_t)s[1]) + (uint64_t)s[2]) + (uint64_t)s[3]) + (uint64_t)s[4]) + (uint64_t)s[5]) + (uint64_t)s[6]) + (uint64_t)s[7]) + (uint64_t)s[8]) + (uint64_t)s[9]) + (uint64_t)s[10]) + (uint64_t)s[11]) + (uint64_t)s[12]) + (uint64_t)s[13]) + (uint64_t)s[14]) + (uint64_t)s[15]) % UINT64_C(2013265921)) + (UINT64_C(1761607681) * (uint64_t)s[11])) % UINT64_C(2013265921));
    t[12] = (((((((((((((((((((UINT64_C(0) + (uint64_t)s[0]) + (uint64_t)s[1]) + (uint64_t)s[2]) + (uint64_t)s[3]) + (uint64_t)s[4]) + (uint64_t)s[5]) + (uint64_t)s[6]) + (uint64_t)s[7]) + (uint64_t)s[8]) + (uint64_t)s[9]) + (uint64_t)s[10]) + (uint64_t)s[11]) + (uint64_t)s[12]) + (uint64_t)s[13]) + (uint64_t)s[14]) + (uint64_t)s[15]) % UINT64_C(2013265921)) + (UINT64_C(2013265906) * (uint64_t)s[12])) % UINT64_C(2013265921));
    t[13] = (((((((((((((((((((UINT64_C(0) + (uint64_t)s[0]) + (uint64_t)s[1]) + (uint64_t)s[2]) + (uint64_t)s[3]) + (uint64_t)s[4]) + (uint64_t)s[5]) + (uint64_t)s[6]) + (uint64_t)s[7]) + (uint64_t)s[8]) + (uint64_t)s[9]) + (uint64_t)s[10]) + (uint64_t)s[11]) + (uint64_t)s[12]) + (uint64_t)s[13]) + (uint64_t)s[14]) + (uint64_t)s[15]) % UINT64_C(2013265921)) + (UINT64_C(7864320) * (uint64_t)s[13])) % UINT64_C(2013265921));
    t[14] = (((((((((((((((((((UINT64_C(0) + (uint64_t)s[0]) + (uint64_t)s[1]) + (uint64_t)s[2]) + (uint64_t)s[3]) + (uint64_t)s[4]) + (uint64_t)s[5]) + (uint64_t)s[6]) + (uint64_t)s[7]) + (uint64_t)s[8]) + (uint64_t)s[9]) + (uint64_t)s[10]) + (uint64_t)s[11]) + (uint64_t)s[12]) + (uint64_t)s[13]) + (uint64_t)s[14]) + (uint64_t)s[15]) % UINT64_C(2013265921)) + (UINT64_C(125829120) * (uint64_t)s[14])) % UINT64_C(2013265921));
    t[15] = (((((((((((((((((((UINT64_C(0) + (uint64_t)s[0]) + (uint64_t)s[1]) + (uint64_t)s[2]) + (uint64_t)s[3]) + (uint64_t)s[4]) + (uint64_t)s[5]) + (uint64_t)s[6]) + (uint64_t)s[7]) + (uint64_t)s[8]) + (uint64_t)s[9]) + (uint64_t)s[10]) + (uint64_t)s[11]) + (uint64_t)s[12]) + (uint64_t)s[13]) + (uint64_t)s[14]) + (uint64_t)s[15]) % UINT64_C(2013265921)) + (UINT64_C(15) * (uint64_t)s[15])) % UINT64_C(2013265921));
    for (int i = 0; i < 16; i++) s[i] = (uint32_t)t[i];
}

static void av_p2_layer8(uint32_t s[16]) {
    uint64_t t[16];
    t[0] = av_p2_sbox(((uint64_t)s[0] + UINT64_C(1765533241)));
    t[1] = (uint64_t)s[1];
    t[2] = (uint64_t)s[2];
    t[3] = (uint64_t)s[3];
    t[4] = (uint64_t)s[4];
    t[5] = (uint64_t)s[5];
    t[6] = (uint64_t)s[6];
    t[7] = (uint64_t)s[7];
    t[8] = (uint64_t)s[8];
    t[9] = (uint64_t)s[9];
    t[10] = (uint64_t)s[10];
    t[11] = (uint64_t)s[11];
    t[12] = (uint64_t)s[12];
    t[13] = (uint64_t)s[13];
    t[14] = (uint64_t)s[14];
    t[15] = (uint64_t)s[15];
    for (int i = 0; i < 16; i++) s[i] = (uint32_t)t[i];
}

static void av_p2_layer9(uint32_t s[16]) {
    uint64_t t[16];
    t[0] = av_p2_sbox(((uint64_t)s[0] + UINT64_C(945325693)));
    t[1] = (uint64_t)s[1];
    t[2] = (uint64_t)s[2];
    t[3] = (uint64_t)s[3];
    t[4] = (uint64_t)s[4];
    t[5] = (uint64_t)s[5];
    t[6] = (uint64_t)s[6];
    t[7] = (uint64_t)s[7];
    t[8] = (uint64_t)s[8];
    t[9] = (uint64_t)s[9];
    t[10] = (uint64_t)s[10];
    t[11] = (uint64_t)s[11];
    t[12] = (uint64_t)s[12];
    t[13] = (uint64_t)s[13];
    t[14] = (uint64_t)s[14];
    t[15] = (uint64_t)s[15];
    for (int i = 0; i < 16; i++) s[i] = (uint32_t)t[i];
}

static void av_p2_layer10(uint32_t s[16]) {
    uint64_t t[16];
    t[0] = av_p2_sbox(((uint64_t)s[0] + UINT64_C(422793067)));
    t[1] = (uint64_t)s[1];
    t[2] = (uint64_t)s[2];
    t[3] = (uint64_t)s[3];
    t[4] = (uint64_t)s[4];
    t[5] = (uint64_t)s[5];
    t[6] = (uint64_t)s[6];
    t[7] = (uint64_t)s[7];
    t[8] = (uint64_t)s[8];
    t[9] = (uint64_t)s[9];
    t[10] = (uint64_t)s[10];
    t[11] = (uint64_t)s[11];
    t[12] = (uint64_t)s[12];
    t[13] = (uint64_t)s[13];
    t[14] = (uint64_t)s[14];
    t[15] = (uint64_t)s[15];
    for (int i = 0; i < 16; i++) s[i] = (uint32_t)t[i];
}

static void av_p2_layer11(uint32_t s[16]) {
    uint64_t t[16];
    t[0] = av_p2_sbox(((uint64_t)s[0] + UINT64_C(311365592)));
    t[1] = (uint64_t)s[1];
    t[2] = (uint64_t)s[2];
    t[3] = (uint64_t)s[3];
    t[4] = (uint64_t)s[4];
    t[5] = (uint64_t)s[5];
    t[6] = (uint64_t)s[6];
    t[7] = (uint64_t)s[7];
    t[8] = (uint64_t)s[8];
    t[9] = (uint64_t)s[9];
    t[10] = (uint64_t)s[10];
    t[11] = (uint64_t)s[11];
    t[12] = (uint64_t)s[12];
    t[13] = (uint64_t)s[13];
    t[14] = (uint64_t)s[14];
    t[15] = (uint64_t)s[15];
    for (int i = 0; i < 16; i++) s[i] = (uint32_t)t[i];
}

static void av_p2_layer12(uint32_t s[16]) {
    uint64_t t[16];
    t[0] = av_p2_sbox(((uint64_t)s[0] + UINT64_C(1311448267)));
    t[1] = (uint64_t)s[1];
    t[2] = (uint64_t)s[2];
    t[3] = (uint64_t)s[3];
    t[4] = (uint64_t)s[4];
    t[5] = (uint64_t)s[5];
    t[6] = (uint64_t)s[6];
    t[7] = (uint64_t)s[7];
    t[8] = (uint64_t)s[8];
    t[9] = (uint64_t)s[9];
    t[10] = (uint64_t)s[10];
    t[11] = (uint64_t)s[11];
    t[12] = (uint64_t)s[12];
    t[13] = (uint64_t)s[13];
    t[14] = (uint64_t)s[14];
    t[15] = (uint64_t)s[15];
    for (int i = 0; i < 16; i++) s[i] = (uint32_t)t[i];
}

static void av_p2_layer13(uint32_t s[16]) {
    uint64_t t[16];
    t[0] = av_p2_sbox(((uint64_t)s[0] + UINT64_C(1629555936)));
    t[1] = (uint64_t)s[1];
    t[2] = (uint64_t)s[2];
    t[3] = (uint64_t)s[3];
    t[4] = (uint64_t)s[4];
    t[5] = (uint64_t)s[5];
    t[6] = (uint64_t)s[6];
    t[7] = (uint64_t)s[7];
    t[8] = (uint64_t)s[8];
    t[9] = (uint64_t)s[9];
    t[10] = (uint64_t)s[10];
    t[11] = (uint64_t)s[11];
    t[12] = (uint64_t)s[12];
    t[13] = (uint64_t)s[13];
    t[14] = (uint64_t)s[14];
    t[15] = (uint64_t)s[15];
    for (int i = 0; i < 16; i++) s[i] = (uint32_t)t[i];
}

static void av_p2_layer14(uint32_t s[16]) {
    uint64_t t[16];
    t[0] = av_p2_sbox(((uint64_t)s[0] + UINT64_C(1009879353)));
    t[1] = (uint64_t)s[1];
    t[2] = (uint64_t)s[2];
    t[3] = (uint64_t)s[3];
    t[4] = (uint64_t)s[4];
    t[5] = (uint64_t)s[5];
    t[6] = (uint64_t)s[6];
    t[7] = (uint64_t)s[7];
    t[8] = (uint64_t)s[8];
    t[9] = (uint64_t)s[9];
    t[10] = (uint64_t)s[10];
    t[11] = (uint64_t)s[11];
    t[12] = (uint64_t)s[12];
    t[13] = (uint64_t)s[13];
    t[14] = (uint64_t)s[14];
    t[15] = (uint64_t)s[15];
    for (int i = 0; i < 16; i++) s[i] = (uint32_t)t[i];
}

static void av_p2_layer15(uint32_t s[16]) {
    uint64_t t[16];
    t[0] = av_p2_sbox(((uint64_t)s[0] + UINT64_C(190525218)));
    t[1] = (uint64_t)s[1];
    t[2] = (uint64_t)s[2];
    t[3] = (uint64_t)s[3];
    t[4] = (uint64_t)s[4];
    t[5] = (uint64_t)s[5];
    t[6] = (uint64_t)s[6];
    t[7] = (uint64_t)s[7];
    t[8] = (uint64_t)s[8];
    t[9] = (uint64_t)s[9];
    t[10] = (uint64_t)s[10];
    t[11] = (uint64_t)s[11];
    t[12] = (uint64_t)s[12];
    t[13] = (uint64_t)s[13];
    t[14] = (uint64_t)s[14];
    t[15] = (uint64_t)s[15];
    for (int i = 0; i < 16; i++) s[i] = (uint32_t)t[i];
}

static void av_p2_layer16(uint32_t s[16]) {
    uint64_t t[16];
    t[0] = av_p2_sbox(((uint64_t)s[0] + UINT64_C(786108885)));
    t[1] = (uint64_t)s[1];
    t[2] = (uint64_t)s[2];
    t[3] = (uint64_t)s[3];
    t[4] = (uint64_t)s[4];
    t[5] = (uint64_t)s[5];
    t[6] = (uint64_t)s[6];
    t[7] = (uint64_t)s[7];
    t[8] = (uint64_t)s[8];
    t[9] = (uint64_t)s[9];
    t[10] = (uint64_t)s[10];
    t[11] = (uint64_t)s[11];
    t[12] = (uint64_t)s[12];
    t[13] = (uint64_t)s[13];
    t[14] = (uint64_t)s[14];
    t[15] = (uint64_t)s[15];
    for (int i = 0; i < 16; i++) s[i] = (uint32_t)t[i];
}

static void av_p2_layer17(uint32_t s[16]) {
    uint64_t t[16];
    t[0] = av_p2_sbox(((uint64_t)s[0] + UINT64_C(557776863)));
    t[1] = (uint64_t)s[1];
    t[2] = (uint64_t)s[2];
    t[3] = (uint64_t)s[3];
    t[4] = (uint64_t)s[4];
    t[5] = (uint64_t)s[5];
    t[6] = (uint64_t)s[6];
    t[7] = (uint64_t)s[7];
    t[8] = (uint64_t)s[8];
    t[9] = (uint64_t)s[9];
    t[10] = (uint64_t)s[10];
    t[11] = (uint64_t)s[11];
    t[12] = (uint64_t)s[12];
    t[13] = (uint64_t)s[13];
    t[14] = (uint64_t)s[14];
    t[15] = (uint64_t)s[15];
    for (int i = 0; i < 16; i++) s[i] = (uint32_t)t[i];
}

static void av_p2_layer18(uint32_t s[16]) {
    uint64_t t[16];
    t[0] = av_p2_sbox(((uint64_t)s[0] + UINT64_C(212616710)));
    t[1] = (uint64_t)s[1];
    t[2] = (uint64_t)s[2];
    t[3] = (uint64_t)s[3];
    t[4] = (uint64_t)s[4];
    t[5] = (uint64_t)s[5];
    t[6] = (uint64_t)s[6];
    t[7] = (uint64_t)s[7];
    t[8] = (uint64_t)s[8];
    t[9] = (uint64_t)s[9];
    t[10] = (uint64_t)s[10];
    t[11] = (uint64_t)s[11];
    t[12] = (uint64_t)s[12];
    t[13] = (uint64_t)s[13];
    t[14] = (uint64_t)s[14];
    t[15] = (uint64_t)s[15];
    for (int i = 0; i < 16; i++) s[i] = (uint32_t)t[i];
}

static void av_p2_layer19(uint32_t s[16]) {
    uint64_t t[16];
    t[0] = av_p2_sbox(((uint64_t)s[0] + UINT64_C(605745517)));
    t[1] = (uint64_t)s[1];
    t[2] = (uint64_t)s[2];
    t[3] = (uint64_t)s[3];
    t[4] = (uint64_t)s[4];
    t[5] = (uint64_t)s[5];
    t[6] = (uint64_t)s[6];
    t[7] = (uint64_t)s[7];
    t[8] = (uint64_t)s[8];
    t[9] = (uint64_t)s[9];
    t[10] = (uint64_t)s[10];
    t[11] = (uint64_t)s[11];
    t[12] = (uint64_t)s[12];
    t[13] = (uint64_t)s[13];
    t[14] = (uint64_t)s[14];
    t[15] = (uint64_t)s[15];
    for (int i = 0; i < 16; i++) s[i] = (uint32_t)t[i];
}

static void av_p2_layer20(uint32_t s[16]) {
    uint64_t t[16];
    t[0] = av_p2_sbox(((uint64_t)s[0] + UINT64_C(1922082829)));
    t[1] = av_p2_sbox(((uint64_t)s[1] + UINT64_C(1870549801)));
    t[2] = av_p2_sbox(((uint64_t)s[2] + UINT64_C(1502529704)));
    t[3] = av_p2_sbox(((uint64_t)s[3] + UINT64_C(1990744480)));
    t[4] = av_p2_sbox(((uint64_t)s[4] + UINT64_C(1700391016)));
    t[5] = av_p2_sbox(((uint64_t)s[5] + UINT64_C(1702593455)));
    t[6] = av_p2_sbox(((uint64_t)s[6] + UINT64_C(321330495)));
    t[7] = av_p2_sbox(((uint64_t)s[7] + UINT64_C(528965731)));
    t[8] = av_p2_sbox(((uint64_t)s[8] + UINT64_C(183414327)));
    t[9] = av_p2_sbox(((uint64_t)s[9] + UINT64_C(1886297254)));
    t[10] = av_p2_sbox(((uint64_t)s[10] + UINT64_C(1178602734)));
    t[11] = av_p2_sbox(((uint64_t)s[11] + UINT64_C(1923111974)));
    t[12] = av_p2_sbox(((uint64_t)s[12] + UINT64_C(744004766)));
    t[13] = av_p2_sbox(((uint64_t)s[13] + UINT64_C(549271463)));
    t[14] = av_p2_sbox(((uint64_t)s[14] + UINT64_C(1781349648)));
    t[15] = av_p2_sbox(((uint64_t)s[15] + UINT64_C(542259047)));
    for (int i = 0; i < 16; i++) s[i] = (uint32_t)t[i];
}

static void av_p2_layer21(uint32_t s[16]) {
    uint64_t t[16];
    t[0] = av_p2_sbox(((uint64_t)s[0] + UINT64_C(1536158148)));
    t[1] = av_p2_sbox(((uint64_t)s[1] + UINT64_C(715456982)));
    t[2] = av_p2_sbox(((uint64_t)s[2] + UINT64_C(503426110)));
    t[3] = av_p2_sbox(((uint64_t)s[3] + UINT64_C(340311124)));
    t[4] = av_p2_sbox(((uint64_t)s[4] + UINT64_C(1558555932)));
    t[5] = av_p2_sbox(((uint64_t)s[5] + UINT64_C(1226350925)));
    t[6] = av_p2_sbox(((uint64_t)s[6] + UINT64_C(742828095)));
    t[7] = av_p2_sbox(((uint64_t)s[7] + UINT64_C(1338992758)));
    t[8] = av_p2_sbox(((uint64_t)s[8] + UINT64_C(1641600456)));
    t[9] = av_p2_sbox(((uint64_t)s[9] + UINT64_C(1843351545)));
    t[10] = av_p2_sbox(((uint64_t)s[10] + UINT64_C(301835475)));
    t[11] = av_p2_sbox(((uint64_t)s[11] + UINT64_C(43203215)));
    t[12] = av_p2_sbox(((uint64_t)s[12] + UINT64_C(386838401)));
    t[13] = av_p2_sbox(((uint64_t)s[13] + UINT64_C(1520185679)));
    t[14] = av_p2_sbox(((uint64_t)s[14] + UINT64_C(1235297680)));
    t[15] = av_p2_sbox(((uint64_t)s[15] + UINT64_C(904680097)));
    for (int i = 0; i < 16; i++) s[i] = (uint32_t)t[i];
}

static void av_p2_layer22(uint32_t s[16]) {
    uint64_t t[16];
    t[0] = av_p2_sbox(((uint64_t)s[0] + UINT64_C(1491801617)));
    t[1] = av_p2_sbox(((uint64_t)s[1] + UINT64_C(1581784677)));
    t[2] = av_p2_sbox(((uint64_t)s[2] + UINT64_C(913384905)));
    t[3] = av_p2_sbox(((uint64_t)s[3] + UINT64_C(247083962)));
    t[4] = av_p2_sbox(((uint64_t)s[4] + UINT64_C(532844013)));
    t[5] = av_p2_sbox(((uint64_t)s[5] + UINT64_C(107190701)));
    t[6] = av_p2_sbox(((uint64_t)s[6] + UINT64_C(213827818)));
    t[7] = av_p2_sbox(((uint64_t)s[7] + UINT64_C(1979521776)));
    t[8] = av_p2_sbox(((uint64_t)s[8] + UINT64_C(1358282574)));
    t[9] = av_p2_sbox(((uint64_t)s[9] + UINT64_C(1681743681)));
    t[10] = av_p2_sbox(((uint64_t)s[10] + UINT64_C(1867507480)));
    t[11] = av_p2_sbox(((uint64_t)s[11] + UINT64_C(1530706910)));
    t[12] = av_p2_sbox(((uint64_t)s[12] + UINT64_C(507181886)));
    t[13] = av_p2_sbox(((uint64_t)s[13] + UINT64_C(695185447)));
    t[14] = av_p2_sbox(((uint64_t)s[14] + UINT64_C(1172395131)));
    t[15] = av_p2_sbox(((uint64_t)s[15] + UINT64_C(1250800299)));
    for (int i = 0; i < 16; i++) s[i] = (uint32_t)t[i];
}

static void av_p2_layer23(uint32_t s[16]) {
    uint64_t t[16];
    t[0] = av_p2_sbox(((uint64_t)s[0] + UINT64_C(1503161625)));
    t[1] = av_p2_sbox(((uint64_t)s[1] + UINT64_C(817684387)));
    t[2] = av_p2_sbox(((uint64_t)s[2] + UINT64_C(498481458)));
    t[3] = av_p2_sbox(((uint64_t)s[3] + UINT64_C(494676004)));
    t[4] = av_p2_sbox(((uint64_t)s[4] + UINT64_C(1404253825)));
    t[5] = av_p2_sbox(((uint64_t)s[5] + UINT64_C(108246855)));
    t[6] = av_p2_sbox(((uint64_t)s[6] + UINT64_C(59414691)));
    t[7] = av_p2_sbox(((uint64_t)s[7] + UINT64_C(744214112)));
    t[8] = av_p2_sbox(((uint64_t)s[8] + UINT64_C(890862029)));
    t[9] = av_p2_sbox(((uint64_t)s[9] + UINT64_C(1342765939)));
    t[10] = av_p2_sbox(((uint64_t)s[10] + UINT64_C(1417398904)));
    t[11] = av_p2_sbox(((uint64_t)s[11] + UINT64_C(1897591937)));
    t[12] = av_p2_sbox(((uint64_t)s[12] + UINT64_C(1066647396)));
    t[13] = av_p2_sbox(((uint64_t)s[13] + UINT64_C(1682806907)));
    t[14] = av_p2_sbox(((uint64_t)s[14] + UINT64_C(1015795079)));
    t[15] = av_p2_sbox(((uint64_t)s[15] + UINT64_C(1619482808)));
    for (int i = 0; i < 16; i++) s[i] = (uint32_t)t[i];
}

/*  The program: 52 layers, inputs any uint32_t. */
static void av_p2_prog(uint32_t s[16]) {
    av_p2_layer0(s);
    av_p2_layer1(s);
    av_p2_layer2(s);
    av_p2_layer0(s);
    av_p2_layer1(s);
    av_p2_layer3(s);
    av_p2_layer0(s);
    av_p2_layer1(s);
    av_p2_layer4(s);
    av_p2_layer0(s);
    av_p2_layer1(s);
    av_p2_layer5(s);
    av_p2_layer0(s);
    av_p2_layer1(s);
    av_p2_layer6(s);
    av_p2_layer7(s);
    av_p2_layer8(s);
    av_p2_layer7(s);
    av_p2_layer9(s);
    av_p2_layer7(s);
    av_p2_layer10(s);
    av_p2_layer7(s);
    av_p2_layer11(s);
    av_p2_layer7(s);
    av_p2_layer12(s);
    av_p2_layer7(s);
    av_p2_layer13(s);
    av_p2_layer7(s);
    av_p2_layer14(s);
    av_p2_layer7(s);
    av_p2_layer15(s);
    av_p2_layer7(s);
    av_p2_layer16(s);
    av_p2_layer7(s);
    av_p2_layer17(s);
    av_p2_layer7(s);
    av_p2_layer18(s);
    av_p2_layer7(s);
    av_p2_layer19(s);
    av_p2_layer7(s);
    av_p2_layer20(s);
    av_p2_layer0(s);
    av_p2_layer1(s);
    av_p2_layer21(s);
    av_p2_layer0(s);
    av_p2_layer1(s);
    av_p2_layer22(s);
    av_p2_layer0(s);
    av_p2_layer1(s);
    av_p2_layer23(s);
    av_p2_layer0(s);
    av_p2_layer1(s);
}
