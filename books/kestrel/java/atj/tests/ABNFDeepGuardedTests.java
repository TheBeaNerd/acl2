/*
 * Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
 * License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
 * Author: Alessandro Coglio (coglio@kestrel.edu)
 */

// This file is handwritten (not generated)
// for the reason given at the end  of the file abnf.lisp.
// However, it is structured similarly to the test code generated by ATJ.

import edu.kestrel.acl2.aij.*;

public class ABNFDeepGuardedTests {

    // Obtain an ACL2 list of natural numbers from the specified file.
    private static Acl2Value getInputFromFile(String filename)
        throws java.io.FileNotFoundException, java.io.IOException {
        java.io.FileInputStream file = new java.io.FileInputStream(filename);
        java.util.List<Integer> bytes = new java.util.ArrayList<>();
        int byt = file.read();
        while (byt != -1) { // EOF
            bytes.add(byt);
            byt = file.read();
        }
        file.close();
        java.util.Collections.reverse(bytes);
        Acl2Value list = Acl2Symbol.NIL;
        for (Integer nat : bytes)
            list = Acl2ConsPair.make(Acl2Integer.make(nat), list);
        return list;
    }

    private static boolean failures = false;

    private static void test_Parse(String testName, Acl2Value input, int n)
        throws Acl2UndefinedPackageException,
               java.io.FileNotFoundException, java.io.IOException {
        System.out.print("Testing '" + testName + "'...");
        Acl2Value[] functionArguments = new Acl2Value[]{input};
        Acl2Symbol functionName = Acl2Symbol.make("ABNF", "PARSE-GRAMMAR");
        boolean pass = true;
        long[] times = n != 0 ? new long[n] : null;
        long minTime = 0;
        long maxTime = 0;
        long sumTime = 0;
        int i = 0;
        do {
            long startTime = System.currentTimeMillis();
            Acl2Value resultJava = ABNFDeepGuarded.call(functionName,
                                                        functionArguments);
            long endTime = System.currentTimeMillis();
            // we just check that the result is not nil:
            pass = pass && !Acl2Symbol.NIL.equals(resultJava);
            if (n != 0) {
                long time = endTime - startTime;
                times[i] = time;
                sumTime = sumTime + time;
                if (i == 0 || time < minTime) {
                    minTime = time;
                }
                if (time > maxTime) {
                    maxTime = time;
                }
            }
            ++i;
        } while (i < n);
        if (pass) {
            System.out.println(" PASS");
        } else {
            System.out.println(" FAIL");
            failures = true;
        }
        if (n != 0) {
            System.out.println("  Times:");
            for (i = 0; i < n; ++i) {
                System.out.format("    %.3f%n", times[i] / 1000.0);
            }
            System.out.format("  Minimum: %.3f%n", minTime / 1000.0);
            System.out.format("  Average: %.3f%n", sumTime / 1000.0 / n);
            System.out.format("  Maximum: %.3f%n", maxTime / 1000.0);
            System.out.println();
        }
    }

    private static void test_ParseABNF(int n)
        throws Acl2UndefinedPackageException,
               java.io.FileNotFoundException, java.io.IOException {
        String testName = "ParseABNF";
        Acl2Value input = getInputFromFile("abnf-files/abnf.txt");
        test_Parse(testName, input, n);
    }

    private static void test_ParseJSON(int n)
        throws Acl2UndefinedPackageException,
               java.io.FileNotFoundException, java.io.IOException {
        String testName = "ParseJSON";
        Acl2Value input = getInputFromFile("abnf-files/json.txt");
        test_Parse(testName, input, n);
    }

    private static void test_ParseURI(int n)
        throws Acl2UndefinedPackageException,
               java.io.FileNotFoundException, java.io.IOException {
        String testName = "ParseURI";
        Acl2Value input = getInputFromFile("abnf-files/uri.txt");
        test_Parse(testName, input, n);
    }

    private static void test_ParseHTTP(int n)
        throws Acl2UndefinedPackageException,
               java.io.FileNotFoundException, java.io.IOException {
        String testName = "ParseHTTP";
        Acl2Value input = getInputFromFile("abnf-files/http.txt");
        test_Parse(testName, input, n);
    }

    private static void test_ParseIMF(int n)
        throws Acl2UndefinedPackageException,
               java.io.FileNotFoundException, java.io.IOException {
        String testName = "ParseIMF";
        Acl2Value input = getInputFromFile("abnf-files/imf.txt");
        test_Parse(testName, input, n);
    }

    private static void test_ParseSMTP(int n)
        throws Acl2UndefinedPackageException,
               java.io.FileNotFoundException, java.io.IOException {
        String testName = "ParseSMTP";
        Acl2Value input = getInputFromFile("abnf-files/smtp.txt");
        test_Parse(testName, input, n);
    }

    private static void test_ParseIMAP(int n)
        throws Acl2UndefinedPackageException,
               java.io.FileNotFoundException, java.io.IOException {
        String testName = "ParseIMAP";
        Acl2Value input = getInputFromFile("abnf-files/imap.txt");
        test_Parse(testName, input, n);
    }

    public static void main(String[] args)
        throws Acl2UndefinedPackageException,
               java.io.FileNotFoundException, java.io.IOException {
        int n = 0;
        if (args.length == 1) {
            n = Integer.parseInt(args[0]);
        }
        if (args.length > 1) {
            throw new IllegalArgumentException("There must be 0 or 1 arguments.");
        }
        ABNFDeepGuarded.initialize();
        test_ParseABNF(n);
        test_ParseJSON(n);
        test_ParseURI(n);
        test_ParseHTTP(n);
        test_ParseIMF(n);
        test_ParseSMTP(n);
        test_ParseIMAP(n);
        if (failures) {
            System.out.println("Some tests failed.");
            System.exit(1);
        } else {
            System.out.println("All tests passed.");
            System.exit(0);
        }
    }
}
