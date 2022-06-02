package uk.robevans.loopringj;

//from ..field import SNARK_SCALAR_FIELD

import com.google.common.math.BigIntegerMath;
import org.bouncycastle.crypto.digests.Blake2bDigest;

import java.math.BigInteger;
import java.math.RoundingMode;
import java.nio.ByteBuffer;
import java.nio.ByteOrder;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

public class Poseidon {

    private static final Map<String, Map> PoseidonParamsType = new ConcurrentHashMap();

    public static final BigInteger SNARK_SCALAR_FIELD = new BigInteger("21888242871839275222246405745257275088548364400416034343698204186575808495617");
    private final int t = 6;
    private final int nRoundsF = 8;
    private final int nRoundsP = 57;
    private final byte[] seed = "poseidon".getBytes(StandardCharsets.UTF_8);
    private final int e = 5;
    private final Integer[] constants_C = null;
    private final Double[][] constants_M = null;
    private final int security_target = 126;

    public Poseidon() {
        HashMap params = new HashMap<String, String>();
        PoseidonParamsType.put("PoseidonParams", params);
        params.put("p", null);
        params.put("t", null);
        params.put("nRoundsF", null);
        params.put("nRoundsP", null);
        params.put("seed", null);
        params.put("e", null);
        params.put("constants_C", null);
        params.put("constants_M", null);
        params.put("security_target", null);
    }

    public Poseidon(BigInteger p, int t, int nRoundsF, int nRoundsP,
                    byte[] seed, int e, BigInteger[] constants_C,
                    Double[][] constants_M, Double security_target) {
        HashMap params = new HashMap<String, String>();
        PoseidonParamsType.put("PoseidonParams", params);
        params.put("p", p);
        params.put("t", t);
        params.put("nRoundsF", nRoundsF);
        params.put("nRoundsP", nRoundsP);
        params.put("seed", seed);
        params.put("e", e);
        params.put("constants_C", constants_C);
        params.put("constants_M", constants_M);
        params.put("security_target", security_target);
    }

    public Map<String, Map> poseidon_params(BigInteger p, int t, int nRoundsF, int nRoundsP,
                                byte[] seed, int e, BigInteger[] constants_C,
                                Double[][] constants_M, Double security_target) {
        if (nRoundsF % 2 != 0 && nRoundsF <= 0
                && nRoundsP <= 0 && t < 2) {
            throw new RuntimeException();
        }


        BigInteger n = BigInteger.valueOf(BigIntegerMath.log2(p, RoundingMode.FLOOR));
        BigInteger M = null;
        if (security_target == null) {
            M = n;  // security target, in bits
        } else {
            M = BigInteger.valueOf(security_target.longValue());
        }
        if (n.compareTo(M) < 0) {
            throw new RuntimeException("n must be greater than M");
        }

        // Size of the state (in bits)
        Double N = Double.valueOf(n.intValue() * t);
        Double grobner_attack_ratio_rounds = 0d;
        Double grobner_attack_ratio_sboxes = 0d;
        Double interpolation_attack_ratio = 0d;

        if (p.mod(BigInteger.valueOf(2)) == BigInteger.valueOf(3)) {
            assert (e == 3);
            grobner_attack_ratio_rounds = 0.32;
            grobner_attack_ratio_sboxes = 0.18;
            interpolation_attack_ratio = 0.63;
        } else if (p.mod(BigInteger.valueOf(5)) != BigInteger.valueOf(1)) {
            assert (e == 5);
            grobner_attack_ratio_rounds = 0.21;
            grobner_attack_ratio_sboxes = 0.14;
            interpolation_attack_ratio = 0.43;
        } else {
            // XXX: in other cases use, can we use 7?
            throw new RuntimeException("Invalid p for congruency");
        }

        Integer nInt = n.intValue();
        Integer MInt = M.intValue();

        // Verify that the parameter choice exceeds the recommendations to prevent attacks
        // iacr.org/2019/458 § 3 Cryptanalysis Summary of Starkad and Poseidon Hashes (pg 10)
        // Figure 1
        // print('(nRoundsF + nRoundsP)', (nRoundsF + nRoundsP))
        // print('Interpolation Attackable Rounds', ((interpolation_attack_ratio * min(n, M)) + log2(t)))
        assert (nRoundsF + nRoundsP) > ((interpolation_attack_ratio * Math.min(nInt, MInt)) + (Math.log(t) / Math.log(2)));
        // Figure 3
        //print('grobner_attack_ratio_rounds', ((2 + min(M, n)) * grobner_attack_ratio_rounds))
        assert (nRoundsF + nRoundsP) > ((2 + Math.min(MInt, nInt)) * grobner_attack_ratio_rounds);
        // Figure 4
        //print('grobner_attack_ratio_sboxes', (M * grobner_attack_ratio_sboxes))
        assert (nRoundsF + (t * nRoundsP)) > (MInt * grobner_attack_ratio_sboxes);

        // iacr.org/2019/458 § 4.1 Minimize "Number of S-Boxes"
        // In order to minimize the number of S-boxes for given `n` and `t`, the goal is to and
        // the best ratio between RP and RF that minimizes:
        //   number of S-Boxes = t · RF + RP
        // - Use S-box x^q
        // - Select R_F to 6 or rhigher
        // - Select R_P that minimizes tRF +RP such that no inequation (1),(3),(4),(5) is satisfied.

        if (constants_C == null) {
            constants_C = poseidon_constants(p, (seed + "_constants").getBytes(StandardCharsets.UTF_8), nRoundsF + nRoundsP);
        }
        if (constants_M == null) {
            constants_M = poseidon_matrix(p, (seed + "_matrix_0000").getBytes(StandardCharsets.UTF_8), t);
        }

        // iacr.org/2019/458 § 4.1 6 SNARKs Application via Poseidon-π
        // page 16 formula (8) and (9)
        Integer n_constraints = (nRoundsF * t) + nRoundsP;
        if (e == 5) {
            n_constraints *= 3;
        } else if (e == 3) {
            n_constraints *= 2;
        }
        //print('n_constraints', n_constraints)
        Map params = PoseidonParamsType.get("PoseidonParams");
        params.put("p", p);
        params.put("t", t);
        params.put("nRoundsF", nRoundsF);
        params.put("nRoundsP", nRoundsP);
        params.put("seed", seed);
        params.put("e", e);
        params.put("constants_C", constants_C);
        params.put("constants_M", constants_M);

        return PoseidonParamsType;
    }


    public byte[]  H(byte[] data) {
        byte[] result = new byte[32];
        byte[] argAs32BitLittleEndianBytes = intTo32BitBytes(data);
        // XXX: ensure that (digest_size*8) >= log2(p)
//        hashed = blake2b(data = arg, digest_size = 32).digest()
        Blake2bDigest hashed = new Blake2bDigest(argAs32BitLittleEndianBytes, 32, new byte[0], new byte[0]);
        hashed.doFinal(result, 0);

        return result;
    }


    public BigInteger[] poseidon_constants(BigInteger p, byte[] seed, int n){
        BigInteger[] typedArray = new BigInteger[n];
        List<BigInteger> result = new ArrayList();
        for(int i=0; i<n; i++) {
            seed = H(seed);
            result.add(BigInteger.valueOf(fromByteArray(seed)).mod(p));
        }
        return result.toArray(typedArray);
    }


    public Double[][] poseidon_matrix(BigInteger p, byte[] seed, int t) {
//        """
//                iacr.org/2019/458 § 2.3 About the MDS Matrix (pg 8)
//                Also:
//                 - https://en.wikipedia.org/wiki/Cauchy_matrix
//                """

        BigInteger[] c = poseidon_constants(p, seed, t * 2);
        Double[][] result = new Double[t][t];
        for (int i=0; i<t; i++) {
            for (int j = 0; j < t; j++) {
                // split this up in to two steps. Ugly as hell but might work
                result[i][j] = Math.pow((c[i].subtract(c[t + j])).mod(p).doubleValue(), p.subtract(BigInteger.valueOf(2)).doubleValue());
                result[i][j] = BigInteger.valueOf(result[i][j].longValue()).mod(p).doubleValue();
            }
        }

        return result;
    }

    public void poseidon_sbox(Double[] state, int i, Map<String, Object> params) {
//            """
//    iacr.org/2019/458 § 2.2 The Hades Strategy (pg 6)
//    In more details, assume R_F = 2 · R_f is an even number. Then
//     - the first R_f rounds have a full S-Box layer,
//     - the middle R_P rounds have a partial S-Box layer (i.e., 1 S-Box layer),
//     - the last R_f rounds have a full S-Box layer
//    """
        Double half_F = Math.floor((Integer)params.get("nRoundsF") / 2);
        Integer e = (Integer) params.get("e");
        Integer p = (Integer) params.get("p");
        if (i<half_F || i >= (half_F + (Integer)params.get("nRoundsP"))) {
            for (int j=0; j < state.length; j++){
                state[j] = Math.pow(state[j], e) % p;
            }
        } else {
            state[0] = Math.pow(state[0], e) % p;
        }
    }


    public Double[] poseidon_mix(Double[] state, Double[][] M, int p) {
//            """
//    The mixing layer is a matrix vector product of the state with the mixing matrix
//     - https://mathinsight.org/matrix_vector_multiplication
//    """
        Double[] result = new Double[M.length];
        for (int i=0; i< M.length; i++) {
            Double sum = 0d;
            for (int j=0; j< state.length; j++){
                sum += M[i][j] * state[j];
            }
            Double columnSumModP = sum % p;
            result[i] = columnSumModP;
        }
        return result;
    }


    public Double poseidon(int[] inputs, Map<String, Object> params, boolean chained, boolean trace) {
//            """
//    Main instansiation of the Poseidon permutation
//    The state is `t` elements wide, there are `F` full-rounds
//    followed by `P` partial rounds, then `F` full rounds again.
//        [    ARK    ]    --,
//         | | | | | |       |
//        [    SBOX   ]       -  Full Round
//         | | | | | |       |
//        [    MIX    ]    --`
//        [    ARK    ]    --,
//         | | | | | |       |
//        [    SBOX   ]       -  Partial Round
//                   |       |   Only 1 element is substituted in partial round
//        [    MIX    ]    --`
//    There are F+P rounds for the full permutation.
//    You can provide `r = N - 2s` bits of input per round, where `s` is the desired
//    security level, in most cases this means you can provide `t-1` inputs with
//    appropriately chosen parameters. The permutation can be 'chained' together
//    to form a sponge construct.
//    """
        if (params == null) {
            params = PoseidonParamsType.get("PoseidonParams");
            if (inputs.length == 0) {
                throw new RuntimeException("expected: inputs.length > 0");
            }
        }
        if (! chained) {
            // Don't allow inputs to exceed the rate, unless in chained mode
            if (inputs.length >= (Integer) params.get("t")) {
                throw new RuntimeException("expected: inputs < " + params.get("t"));
            }
        }
        Double[] state = new Double[(Integer)params.get("t")];
        Arrays.fill(state, 0);

        for (int i=0; i< inputs.length; i++) {
            state[i] = Double.valueOf(inputs[i]);
        }
        for (int i=0; i < ((Integer[]) params.get("constants_C")).length; i++) {
            Integer C_i = ((Integer[]) params.get("constants_C"))[i];
            for (Double value : state) {
                state[i] = value + C_i;  // ARK(.)
            }
            poseidon_sbox(state, i, params);
            state = poseidon_mix(state, (Double[][])params.get("constants_M"), (Integer)params.get("p"));
            if (trace) {
                for (int j = 0; j < state.length; j++) {
                    Double val = state[j];
                    System.out.println("("+i+", " + j +") = " + val);
                }
            }

        }
//        if (chained) {
//            // Provide the full state as output in 'chained' mode
//            return state;
//        }
        return state[0];
    }

    private byte[] intTo32BitBytes(byte[] value) {
        if (value.length < 0 || value.length >= (1L << Integer.SIZE)) {
            throw new IllegalArgumentException("size negative or larger than 32 bits: " + value);
        }

        byte[] header = ByteBuffer
                .allocate(Long.BYTES)
                .order(ByteOrder.LITTLE_ENDIAN)
                .putInt(fromByteArray(value))
                .array();
        return header;
    }

    private Integer fromByteArray(byte[] bytes) {
        return bytes[0] << 24 | (bytes[1] & 0xFF) << 16 | (bytes[2] & 0xFF) << 8 | (bytes[3] & 0xFF);
    }
}
