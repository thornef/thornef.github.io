import java.lang.*;
import java.io.*;
import java.util.*;
import java.math.*;

// CountS3.java, by Frank Thorne
// Please feel free to use, modify, and extend this as you see fit -- but please also cite our paper!

// See also the function extraTest below -- the program can easily be modified to only count field
// discriminants meeting some specified criteria (i.e., coprime to 6)

public class CountS3 {

public static String inputFile = "T31-107.txt"; // read in this file. if args[0] is specified, read that instead.
public static long maxDisc = 10000000; // Assumed to be < 2^31.5 (otherwise longs won't cut it). can override in args[1]
public static double DHConstant = .208; // # of cubic fields with 0 < -Disc(K) < X is .2079... * X - the secondary term + small error.

// some global variables, to be initialized later (once we know what maxDisc is)
public static int possibleDiscs = 0;
public static long maxGCDisc = 0; 
public static long[] discsList; // a list of all S_3 discriminants counted
public static long[] originalDiscsList; // a list of cubic discriminants corresponding to the S_3 discriminants counted
public static long[] allOriginalDiscsList; // a list of all cubic field discriminants processed.
public static int discsCounter = 0;
public static int allDiscsCounter = 0; // counts even discriminants where the S_3 closure has discriminant too big.
public static int squareDiscsCounter = 0; // how many square discriminants we found (and didn't compute the Galois closure)
public static boolean negDiscsFlag = false; // will be set to true (if appropriate) when parsing the file.

public static boolean countAllOriginalDiscs = false; // if this is true, maintain an array of all cubic fields being processed,
						    // even those whose S_3 discriminant is out of bounds. (can consume lots of memory)
                                                    // Note also there is an unfixed bug: Will get array overflow errors in case
                                                    // this is on and the file is large in comparison to how many discs we actually count.

// keep a list of primes around.
public static int maxPrime = 0; // again, to be initialized based on maxDisc
public static int[] primes;
public static int num_primes = 0;

public static void DEBUG(String s) {
  System.out.println(s);
}

public static boolean isPrime(int n) {
  int i;
  boolean retval = true;
  double my_sqrt = Math.round(Math.sqrt((double) n));
  for (i = 2; i < my_sqrt + 0.01; i++) {
    if (n % i == 0) retval = false;
  }
  return retval;
}

public static boolean isSquare(long n) {
  long l = Math.round(Math.sqrt((double) n)); 
  return (l*l == n);
}

// generate a list of primes. (perhaps this already exists in the java language?)

public static void generatePrimes() {
  int[] temp_primes = new int[maxPrime];
  int counter = 0;
  for (int i = 2; i < maxPrime; i++)
    if (isPrime(i))
      temp_primes[counter++] = i;
  primes = new int[counter + 1];
  num_primes = counter + 1;
  for (int i = 0; i < counter; i++)
    primes[i] = temp_primes[i];

  // this is a trick: the last "prime" is a number chosen to be bigger than any prime whose square can divide the discriminant
  // assuming we don't count cubic fields past 10^14.
  // The reason for this is we want to be able to shortcut a loop: test, for each prime, where its square divides the discriminant
  // of a number field. However, whenever we find nonsquare factors, that tells us that we have fewer primes we have to check.
  // We go progressively through the list of primes and make sure that each (in turn) is not too big. By adding one at the end that
  // is definitely "too big" that saves us an additional array index out of bounds check in the innermost loop of the program.
  primes[num_primes - 1] = 10000000;
}

// This is important!!
// is_tr_at_2: given an array of five integers: first four are the cubic form coeffs, last is the discriminant.
// determine if the cubic field is totally ramified at 2, assuming the cubic ring is maximal.
// this can be determined by reducing mod 2, there are 16 possibilities, and there are three that correspond to being totally ramified at 2.
// just do it by brute force.

public static boolean is_tr_at_2(int[] disc_data) {
  boolean a = (Math.abs(disc_data[0]) % 2 == 1);
  boolean b = (Math.abs(disc_data[1]) % 2 == 1);
  boolean c = (Math.abs(disc_data[2]) % 2 == 1);
  boolean d = (Math.abs(disc_data[3]) % 2 == 1);
  boolean retval = false;
  // totally ramified at 2: (1, 1, 1, 1), (1, 0, 0, 0), (0, 0, 0, 1).
  if (a && !b && !c && !d) retval = true;
  if (d && !b && !c && !a) retval = true;
  if (a && b && c && d) retval = true;
  // 1^2: (0, 0, 1, 0), (0, 0, 1, 1), (0, 1, 0, 0), (0, 1, 0, 1), (1, 0, 1, 0), (1, 1, 0, 0)
  
  /* some debugging code: complain if any "bad" cubic forms are seen modulo 2. 
  // Was tested up to -Disc(K) < 10^6 without error.
  // (0, 0, 0, 0): never maximal.
  if (!a && !b && !c && !d) DEBUG("Error 1!" + disc_data[0] + ":" + disc_data[1] + ":" + disc_data[2] + ":" + disc_data[3]);
  // (0, 1, 1, 0): never ramified at 2.
  if (!a && b && c && !d) DEBUG("Error 2!" +disc_data[0] + ":" + disc_data[1] + ":" + disc_data[2] + ":" + disc_data[3]);
  // (0, 1, 1, 1): as above.
  if (!a && b && c && d) DEBUG("Error 3!" +disc_data[0] + ":" + disc_data[1] + ":" + disc_data[2] + ":" + disc_data[3]);
  // (1, 0, 0, 1): as above.
  if (a && !b && !c && d) DEBUG("Error 4!" +disc_data[0] + ":" + disc_data[1] + ":" + disc_data[2] + ":" + disc_data[3]);
  // (1, 0, 1, 1):
  if (a && !b && c && d) DEBUG("Error 5!" +disc_data[0] + ":" + disc_data[1] + ":" + disc_data[2] + ":" + disc_data[3]);
  // (1, 1, 0, 1):
  if (a && b && !c && d) DEBUG("Error 6!" +disc_data[0] + ":" + disc_data[1] + ":" + disc_data[2] + ":" + disc_data[3]);
  // (1, 1, 1, 0): as above.
  if (a && b && c && !d) DEBUG("Error 7!" +disc_data[0] + ":" + disc_data[1] + ":" + disc_data[2] + ":" + disc_data[3]);
  */

  return retval;
}

// compute the discriminant of the Galois closure in terms of the original discriminant.
// there might be some room to improve the efficiency, but it is pretty good as it is.

// ALSO checks to see if the discriminant is larger than the maximum allowed; if it is, returns zero.
// This is a little bit undesirable, but if we don't do this, we can't store the result in a long,
// and so we have to deal with this cumbersome BigInteger class more than we have to already.

public static long gcDisc(int[] disc_data) {
  long disc = disc_data[4];
  BigInteger biDisc = BigInteger.valueOf(disc);
  long maxPrimeToCheck = Math.round(Math.pow(disc, 0.5)); // need to check divisibility by primes up to this.
  
  //Debug code: compare the cubic form discriminant with the discriminant output by Belabas's cubic.
  //Was tested with -Disc(K) < 10^6 without error.
  if (disc != getDisc(disc_data)) 
    DEBUG("Error. discriminant mismatch.");

  BigInteger retval = biDisc.multiply(biDisc.multiply(biDisc));
  if ((disc % 27 == 0) && (disc % 81 != 0)) retval = retval.divide(BigInteger.valueOf(9));
  if ((disc % 81) == 0) retval = retval.divide(BigInteger.valueOf(81));
  if (disc % 4 == 0) {
    if ((disc % 8 != 0) && (is_tr_at_2(disc_data))) retval = retval.divide(BigInteger.valueOf(4));;
    maxPrimeToCheck = maxPrimeToCheck / 2;
  }

  //Results of this loop were demonstrated identical to the more complicated loop below for discs < 10^7.
  //BigInteger retval2 = retval.pow(1);
  //for (int i = 2; i < num_primes; i++) { // start at i = 3 (i.e. the prime 5)
  //  int p = primes[i];
  //  if ((disc % (p*p)) == 0) retval2 = retval2.divide(BigInteger.valueOf(p*p));
  //}
  int i;
  int p = 0;

  i = 2;
  while (primes[i] <= maxPrimeToCheck) {
    p = primes[i];
    if ((disc % p) == 0) {
      if ((disc % (p*p)) == 0) 
        retval = retval.divide(BigInteger.valueOf(p*p));
      else {
        maxPrimeToCheck = (long) Math.round(maxPrimeToCheck / Math.pow(p, 0.5));
      }
    }
   i++;
  }

  /*
  if (retval.compareTo(retval2) != 0) {
    System.out.println("Last prime checked" + p);
    System.out.println("max prime" + maxPrimeToCheck);
    System.out.println(retval);
    System.out.println(retval2); 
    System.out.println(disc);
    System.out.println("-----------");
  }
  */
  if (retval.compareTo(BigInteger.valueOf(maxGCDisc)) != -1) return 0;
  if (retval.longValue() < 0) {
    DEBUG("" + disc_data[0]);
    DEBUG("" + disc_data[1]);
    DEBUG("" + disc_data[2]);
    DEBUG("" + disc_data[3]);
    DEBUG("" + disc_data[4]);
  }
  return retval.longValue();
}

// cubic form discriminant. 
// currently disused; has been checked to match the field discriminant output by
// Belabas's program in many cases.

public static long getDisc(int[] coeffs) {
	long a = coeffs[0];
	long b = coeffs[1];
	long c = coeffs[2];
	long d = coeffs[3];
	long disc = b*b*c*c - 4*a*c*c*c - 4*b*b*b*d - 27*a*a*d*d + 18*a*b*c*d;
	return Math.abs(disc);
}

/*********************************************
Parsing routines:
The next several procedures parse the output from Belabas's cubic. It looks like this:
-23: (-5,-7,1)  [1,1,2,1]
-175: (-5,-25,-5)  [1,1,2,3]
-543: (-5,-43,-11)  [1,1,2,5]

Each line is parsed into an array of five ints -- the last four numbers and then the first one (the discriminant).
Cubic form discriminant has been checked to match the first number when -10^6 < Disc(K) < 0.

There is some error checking done (e.g. if the input file is garbage) but it is far from thorough.
*********************************************/

public static void errorMsg(int oneChar, int expChar) {
    System.out.print("Found unexpected character. Expected: ");
    System.out.print((char) expChar);
    System.out.print(" Found: ");
    System.out.println((char) oneChar);
}

// parse one character, which is expected to be either expChar or EOF.
public static int parseChar(java.io.FileReader fr, int expChar) throws Exception {
  int oneChar = fr.read();
  if ((oneChar != expChar) && (oneChar != -1)) 
    errorMsg(oneChar, expChar);
  return oneChar;
}

// parses an integer from the file and returns it. assumes it is terminated by any character
// other than 0-9, which terminates it.

public static int parseInt(java.io.FileReader fr) throws Exception {
  boolean isFinished = false, minusFlag = false;
  int oneChar;
  int currVal = 0;
  while (! isFinished) {
      oneChar = fr.read();
      if (oneChar == '-') minusFlag = true;
      else if ((oneChar >= 48) && (oneChar <= 57)) {
	int intChar = oneChar - 48;
	currVal = currVal * 10 + intChar;
      }
      else isFinished = true;
  }
  if (minusFlag) currVal = 0 - currVal;
  return currVal;
}

public static void parseRestOfLine(java.io.FileReader fr) throws Exception {
  boolean done = false;
  while (! done) {
    int oneChar = fr.read();
    if ((oneChar == -1) || (oneChar == 10)) done = true;
  }
}

//Parse one line of the file.
//Returns: the four coefficients (note: I am *guessing* these are correct, they are *not* the cubic form)
//followed by the discriminant.

public static int[] parseLine(java.io.FileReader fr) throws Exception {
  boolean errFlag = false;
  int errChar = -2; // -1 is saved for EOF
  int oneChar;
  int[] ret_val = new int[5];
  int d = parseInt(fr); 
  if (d < 0) negDiscsFlag = true;
  int disc = Math.abs(d);
  parseChar(fr, ' ');
  parseChar(fr, '(');
  for (int i = 0; i < 3; i++) parseInt(fr); 
  parseChar(fr, ' ');
  parseChar(fr, ' ');
  parseChar(fr, '[');
  for (int i = 0; i < 4; i++)
    ret_val[i] = parseInt(fr);
  ret_val[4] = disc;
  parseRestOfLine(fr);
  return ret_val;
}

// extraTest: puts an extra test on our discriminant. default is to just return true, unless we only want a selection.

// This is written in a somewhat inefficient manner. E.g., it would be more efficient to test discriminants before computing the 
// discriminant of the galois closure, if possible. (e.g. if we only want to allow discriminants coprime to 2 or 3)
// However this did not seem like it was worth worrying about too much.

public static boolean extraTest(long GCDisc) {
  //return true;
  return ((GCDisc % 6) == 1) || ((GCDisc % 6) == 5);
}

public static void processLine(int[] oneLine) throws Exception {
  if (! negDiscsFlag && isSquare(oneLine[4])) {
    squareDiscsCounter++;
  }
  else {
    long GCDisc = gcDisc(oneLine);
    if (GCDisc != 0 && extraTest(GCDisc)) { // 0 is the code for "too big, don't count"
      discsList[discsCounter] = GCDisc;
      // in addition, save the original discriminants in a separate array
      originalDiscsList[discsCounter++] = oneLine[4];
    }
  }  
  if (countAllOriginalDiscs)
    allOriginalDiscsList[allDiscsCounter] = oneLine[4];
  allDiscsCounter++;
}

public static void processFile() throws Exception {

  FileReader fr = new java.io.FileReader(inputFile);
  boolean eofReached = false;
  while (!eofReached) {
    int[] oneLine = parseLine(fr);
    if (oneLine[0] == 0)
	eofReached = true;
    else
	processLine(oneLine);
  } 
  fr.close();	
}


/*********************************************
There is no serious math below, hopefully the remainder is self explanatory!
*********************************************/

// There must be a better way to write this procedure.
public static void cleanDiscsList() {
  long[] newArray = new long[discsCounter];
  for (int i = 0; i < discsCounter; i++)
    newArray[i] = discsList[i];
  Arrays.sort(newArray); // pity this is so easy, all that time in AP comp sci wasted!
  discsList = newArray;

  long[] newArray2 = new long[discsCounter];
  for (int i = 0; i < discsCounter; i++)
    newArray2[i] = originalDiscsList[i];
  Arrays.sort(newArray2); // pity this is so easy, all that time in AP comp sci wasted!
  originalDiscsList = newArray2;

  if (countAllOriginalDiscs) {
    long[] newArray3 = new long[allDiscsCounter];
    for (int i = 0; i < allDiscsCounter; i++)
      newArray3[i] = allOriginalDiscsList[i];
    Arrays.sort(newArray3); // pity this is so easy, all that time in AP comp sci wasted!
    allOriginalDiscsList = newArray3;
  }
}

public static void testOutput(boolean verbose, boolean extraReport) {
  System.out.print("Number of cubic fields counted: "); // this is here to double check with known counts.
  System.out.println(allDiscsCounter);
  System.out.print("Number of cyclic cubic fields counted: "); // this is here to double check with known counts.
  System.out.println(squareDiscsCounter);
  System.out.print("Sign of discriminants negative: ");
  System.out.println(negDiscsFlag);
  System.out.print("Number of S_3 discriminants counted: ");
  System.out.println(discsCounter);
  if (verbose)
     for (int i = 0; i < discsCounter; i++) {
       System.out.print("Discriminant: ");
       System.out.println(discsList[i]);
     }
  if (extraReport) {
    long[] thresholds = new long[36];
    for (int i = 0; i < 4; i++) {
       long pw = Math.round(Math.pow(10, 4 - i));
       thresholds[9*i] = maxGCDisc / pw;
       thresholds[9*i + 1] = 3 * (maxGCDisc / (2 * pw));
       thresholds[9*i + 2] = 2 * (maxGCDisc / pw);
       thresholds[9*i + 3] = 5 * (maxGCDisc / (2 * pw));
       thresholds[9*i + 4] = 3 * (maxGCDisc / pw);
       thresholds[9*i + 5] = 4 * (maxGCDisc / pw);
       thresholds[9*i + 6] = 5 * (maxGCDisc / pw);
       thresholds[9*i + 7] = 6 * (maxGCDisc / pw);
       thresholds[9*i + 8] = 8 * (maxGCDisc / pw);
    }
   int thresholdCounter = 0;
   for (int i = 0; i < discsCounter; i++) {
     if (thresholdCounter != 36) {
       if (discsList[i] > thresholds[thresholdCounter]) {
        System.out.println("Discriminants < " + thresholds[thresholdCounter] + ": " + i);
	thresholdCounter++;
       }
     }
   }
   System.out.println("Discriminants < " + maxGCDisc + ": " + discsCounter);
  }
}

// Count field discriminants in arithmetic progression.
public static void countAP(int modulus) {
  System.out.println("S_3 discriminants counted, by discriminant of the S_3 field");
  int[] APcounts = new int[modulus];
  for (int i = 0; i < modulus; i++) APcounts[i] = 0;
  for (int i = 0; i < discsCounter; i++) {
    int rc = (int) (discsList[i] % modulus);
    APcounts[rc]++;
  }
  for (int i = 0; i < modulus; i++) {
     System.out.print("" + i + " mod " + modulus + ": " );
     System.out.println(APcounts[i]);
  }
}

// Count field discriminants in arithmetic progression.
// This procedure: count only fields whose Galois closure has bounded discriminant, but
// count the *original* cubic field discrimiants by AP.
// copy-pasted from previous procedure, with only one change :(

public static void countOriginalAP(int modulus) {
  System.out.println("S_3 discriminants counted, by discriminant of the cubic field");
  int[] APcounts = new int[modulus];
  for (int i = 0; i < modulus; i++) APcounts[i] = 0;
  for (int i = 0; i < discsCounter; i++) {
    int rc = (int) (originalDiscsList[i] % modulus);
    APcounts[rc]++;
  }
  for (int i = 0; i < modulus; i++) {
     System.out.print("" + i + " mod " + modulus + ": " );
     System.out.println(APcounts[i]);
  }
}

// count all the fields we looked at by arithmetic progression, regardless of what their S_3 closure was.

// If Matthias Felleisen sees these three look-alike procedures, he will probably look up my undergraduate
// transcripts and retroactively change my grade in intro CS to an F.
 
public static void countAllOriginalAP(int modulus) {
  System.out.println("all cubic discriminants counted (regardless of whether the S_3 discriminant was counted or not)");
  int[] APcounts = new int[modulus];
  for (int i = 0; i < modulus; i++) APcounts[i] = 0;
  for (int i = 0; i < allDiscsCounter; i++) {
    int rc = (int) (allOriginalDiscsList[i] % modulus);
    APcounts[rc]++;
  }
  for (int i = 0; i < modulus; i++) {
     System.out.print("" + i + " mod " + modulus + ": " );
     System.out.println(APcounts[i]);
  }
}
// computes maxGCDisc, the highest discriminant of a Galois closure we are counting.
// Basically 3 * maxDisc^2, but we round down to make the output pretty. 

// note: square root of 10/3 is 1.82574, of 5/3 is 1.29099...
// square root of 100/3 is 5.7735...

public static long computeMaxGCDisc(long maxDisc) {
  long retval = 3 * maxDisc * maxDisc; // the maximum the discriminant of GC of K can be, if Disc(K) < maxdisc.
  long fe18 = 5000000000000000000L;
  if (retval > fe18) retval = fe18;
  
  //optional: round it down to the nearest power of 10 to make the output pretty.
  long logDisc = Math.round(Math.log(retval)/Math.log(10) - 0.5001); // round *down*
  retval = Math.round(Math.pow(10, logDisc));

  return retval;
}

public static void main(String[] args) {
    try {
        long beginTime = new Date().getTime();
	boolean verbose = false;
	if (args.length > 0)
	    inputFile = args[0];
	if (args.length > 1)
	    maxDisc = Long.parseLong(args[1]);
	if (args.length > 2)
	  if (args[2].equals("-v"))
	    verbose = true;
	possibleDiscs = (int) Math.round(Math.pow(maxDisc, 0.67) + 1000);
        maxPrime = (int) Math.round(Math.pow(maxDisc, 0.5) + 3);
	discsList = new long[possibleDiscs];
	originalDiscsList = new long[possibleDiscs];
        if (countAllOriginalDiscs) {
	  int aodlLength = (int) (maxDisc * DHConstant);
	  allOriginalDiscsList = new long[aodlLength];
	} 
	maxGCDisc = computeMaxGCDisc(maxDisc);
	System.out.println(maxDisc);
	System.out.println(maxGCDisc);
	generatePrimes();
	processFile();
	cleanDiscsList();
	testOutput(verbose, true);
	countAP(5);
	countOriginalAP(5);
	// see how long the calculation took
	long endTime = new Date().getTime();
	System.out.println("Milliseconds required: " + (endTime - beginTime));
    }
    catch (Exception e) { e.printStackTrace(); }
}

}