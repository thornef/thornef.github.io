import java.lang.*;
import java.io.*;
import java.util.*;
import java.math.*;

// ParseBelabas.java, by Frank Thorne
// Please feel free to use, modify, and extend this as you see fit -- but please also cite our paper!

// This program parses the output of Karim Belabas's "cubic" program into one or more 
// .gp files. The input has a bunch of lines like this

// -891: (-18,-9,36)  [1,0,6,1]

// and we output lines that look like this

// [1, 0, 6, 1]

// Each output file will contain num_fields_per_file files, and if output_file_base is "css-data" then the output
// will be "css-data-1.gp", "css-data-2.gp", etc. This program can process arbitrarily large data files, but
// the program that uses it cannot.


public class ParseBelabas {

public static String inputFile = "T33-1826-09.txt"; // read in this file. 
public static int num_fields_per_file = 1000000;
public static String output_file_base = "belabas-test";

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

public static void writeLine(java.io.FileWriter fw, int[] oneLine) throws Exception {
  fw.write('[');
  fw.write("" + oneLine[0]);
  fw.write(',');
  fw.write("" + oneLine[1]);
  fw.write(',');
  fw.write("" + oneLine[2]);
  fw.write(',');
  fw.write("" + oneLine[3]);
  fw.write(']');
  fw.write(10);
}

public static void processFile() throws Exception {

  FileReader fr = new java.io.FileReader(inputFile);
  FileWriter fw = null;
  String currFileName = "";
  boolean eofReached = false;
  int lineCounter = 1;
  int fileCounter = 1;
  while (!eofReached) {
    if (lineCounter == 1) {
      currFileName = output_file_base + "-" + fileCounter + ".gp";
      fw = new java.io.FileWriter(currFileName);
    }   
    int[] oneLine = parseLine(fr);
    if (oneLine[0] == 0)
	eofReached = true;
    else {
      writeLine(fw, oneLine);
      lineCounter ++ ;
      if (lineCounter > num_fields_per_file) {
        fw.flush();
        fw.close();
        lineCounter = 1;
        fileCounter ++;
        System.out.print(".");
      }
    }
  } 
  fw.flush();
  fw.close();
  System.out.println("Produced " + fileCounter + " files, last was " +  currFileName + ".");
  System.out.println("Each contains " +  num_fields_per_file +  " cubic fields.");
  System.out.println("Last contains " + lineCounter + " cubic fields.");  
  fr.close();	
}


public static void main(String[] args) {
    try {
        long beginTime = new Date().getTime();
	processFile();
	long endTime = new Date().getTime();
	System.out.println("Milliseconds required: " + (endTime - beginTime));
    }
    catch (Exception e) { e.printStackTrace(); }
}

}