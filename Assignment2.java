/*
    This implements Davis-Putnam
 */
package assignment2;
import java.io.*;// for input from a file
import java.util.Collection;
import java.util.HashMap; //used for the two sets
import java.util.HashSet;
import java.util.Iterator;
import java.util.Queue; //used for the solution
import java.util.stream.Stream; // for input from a file
import java.util.Set;//for sets (not maps)

/**
 * @author Matthew Meeh
 * @date-start: 10/16/2020
 * @date-end: 10/31/2020
 */

public class Assignment2 {

    public static void main(String[] args) throws Exception{
        Assignment2 start = new Assignment2(args);
    }
    
    public Assignment2(String[] args) throws Exception{
        // PARSE the args
        String filename = args[0];
        File file = new File(filename);
        BufferedReader in = new BufferedReader(new FileReader(file));
        String line; int numLines=0;
        String[] Clauses = new String[20];
        HashMap<Integer, Integer> ATOMs_INTEGER = new HashMap<Integer, Integer>();
        String other = "";boolean doneParse = false;
        int clauseCounter = 0; int atomAbsCounter = 0;
        while ( (line = in.readLine()) != null){
            String ATOM = ""; 
            String[] ATOMs = new String[50]; int atomCounter = 0;
            if(doneParse){
                other = other + line + "\n";
            }
            else {
                Clauses[clauseCounter] = line + " ";
                clauseCounter++;
            }
            
            for(int charD =0; charD < line.length(); charD++){
                    if(doneParse){
                        break;
                    }
                    if(line.charAt(charD) == ' '){
                        ATOMs[atomCounter] = ATOM;
                        Integer inte = Integer.parseInt(ATOM);
                        int temp = inte.intValue();
                        temp = Math.abs(temp);
                        inte = temp;
                        ATOM = "";
                        if(!ATOMs_INTEGER.containsKey(inte)){
                            ATOMs_INTEGER.put(inte, inte);
                            atomAbsCounter++;
                            continue;
                        }
                        else {
                            //Contains the ATOM already, don't add
                            continue;
                        }
                    }
                    if(line.charAt(charD) == '0'){
                        doneParse = true;
                        other = line + "\n";
                        break;
                    }
                    else {
                       ATOM = ATOM + line.substring(charD, charD+1); 
                    }
            }
        }
        Clause[] clausesREAL = new Clause[clauseCounter-1];
        for(int i=0;i<clauseCounter-1; i++){
            if(Clauses[i] == ""){//DONE
                break;
            }
            else {
                clausesREAL[i] = new Clause(Clauses[i], i);
            }
        }
        Integer[] atomsTEMP = new Integer[atomAbsCounter];
        int[] atomsREAL = new int[atomAbsCounter];
        Set temp = new HashSet<Integer>();
        temp = ATOMs_INTEGER.keySet();
        temp.toArray(atomsTEMP);
        for(int i=0;i<atomAbsCounter; i++){
            atomsREAL[i] = atomsTEMP[i];
        }
        in.close();
        //DONE parsing
        int[] atoms = new int[] {1, 2, 3} ; //TESTING
        Clause[] clauses = new Clause[] {new Clause("1 2 3 ", 1),new Clause("-2 -3 ", 2),
                new Clause("-3 ", 3)}; // TESTING
        
        David_Putnam_Storage first = new David_Putnam_Storage(atomsREAL, clausesREAL);
        File newFile = new File("output.txt");
        FileWriter writer = new FileWriter(newFile);
        if(first.success_Outer){
        for(int Int=0;Int < first.final_V.length; Int++){
            if(first.final_V[Int].state ){
            writer.write(first.final_V[Int].Atom + " " + "T"+ "\n");}//all the clauses
            else {
            writer.write(first.final_V[Int].Atom + " " + "F"+ "\n");//all the clauses
}
        }
        }
        else {
            writer.write("There is no solution to the problem.\n");
        }
        writer.write(other);//rest of the data
        writer.flush();
        writer.close();
    }
    public class David_Putnam_Storage{
        Specialized_Integer[] final_V; 
        Clause[] secClauses;
        boolean success_Outer;
        //DONE
        public David_Putnam_Storage(int[] Atoms, Clause[] Clauses){
            Specialized_Integer[] V = new Specialized_Integer[Atoms.length];
            for(int atomNum = 0; atomNum < Atoms.length; atomNum++){
                Specialized_Integer tempA = new Specialized_Integer(Atoms[atomNum]);
                V[atomNum] = tempA;
            }
            final_V = new Specialized_Integer[Atoms.length]; //!! May not need this intialization
            final_V = copy(V);
            secClauses = copyC(Clauses);
            boolean success = David_Putnam_Algorithm(V, Clauses, 0, true);
            if(success){
                System.out.println("There exists an solution of the CNF:");
                printV();
                write();
            }
            else {
            
            }
            success_Outer = success;
            
        }
        public void write(){
            
            for(int Int=0;Int < final_V.length; Int++){
                if(final_V[Int].state){
                System.out.println(final_V[Int].Atom + " ");}
                else {
                    System.out.println(final_V[Int].Atom + " F");}
                }
        }
        public Specialized_Integer[] copy(Specialized_Integer[] array){
            Specialized_Integer[] temp = new Specialized_Integer[array.length];
            for(int i=0; i<array.length; i++){
                temp[i] = new Specialized_Integer(array[i].Atom);
                temp[i].state = array[i].state;
                temp[i].hasSet = array[i].hasSet;
            }
            return temp;
        }
        public Clause[] copyC(Clause[] array){
            Clause[] temp = new Clause[array.length];
            for(int i=0; i<array.length; i++){
                temp[i] = new Clause(array[i].passed_Clause, array[i].id);
                temp[i].successEvaluated = false;
            }
            return temp;
        }
        // DONE
        public boolean David_Putnam_Algorithm(Specialized_Integer[] V, Clause[] Clauses, int occurance, boolean valuation){
            boolean ran = true;
            while(ran){
                 //5 
                Clauses = progagate(V, Clauses);
                int evul = evaluationClauses(V, Clauses); //moved here
                
                ran = false;
                
                if(evul == 1){// 1 :: Clauses is null
                    final_V = V;
                    return true;
                }
                if(evul == -1){ // 2 :: Clauses contains null
                    return false;
                }
                Data relational;
                relational = containsSingleSign(Clauses, V);
                int returnValue = relational.foundAt;
                if(returnValue != -1 && V[returnValue].hasSet == false){ // 3
                    ran = true;
                    V[returnValue].state = relational.shouldBe;
                    V[returnValue].hasSet = true;
                    
                }
                relational = containsSingleConditional(Clauses, V);
                returnValue = relational.foundAt;
                if(returnValue != -1 && V[returnValue].hasSet == false){ // 4
                    ran = true;
                    V[returnValue].state = relational.shouldBe;
                    V[returnValue].hasSet = true;
                }
            }// 6 TODO
            //Try to set the [] ATOM to true OR false
            boolean value = false;
            if(occurance == 0 && valuation == false){//added :Back at the begining
                return false;
            }
            if(occurance != V.length && V[occurance].hasSet == false){
                V[occurance].state = true; 
                V[occurance].hasSet = true;
                value = David_Putnam_Algorithm(V, Clauses, occurance+1, true);
            if(occurance == 0 && valuation == false){//added :Back at the begining
                return false;
            }
            if(value){
                return true;
            }
            else {
                final_V = copy(V);
                for(int i=V.length-1; i>occurance; i--){
                    final_V[i].hasSet = false;
                }
                if(valuation){
                final_V[occurance].state = false;
                final_V[occurance].hasSet = true;   
                }
                else {
                final_V[occurance].state = false;
                final_V[occurance].hasSet = true;                   }

                Clauses = copyC(secClauses);
                return David_Putnam_Algorithm(final_V, Clauses, occurance+1, !valuation);
                
            }
            }
            return false; //end of method
        }
        // Working
        public Clause[] progagate(Specialized_Integer[] values, Clause[] S){//TODO
            if(S == null){
                return null;
            }
            for(int i=0; i<S.length; i++){
                for(int j=0; j<values.length;j++){
                    if(S.length == 0){ //re located
                        return null;
                    }
                    if(values[j].hasSet == false){
                        continue; // we reached the end of the line
                    }
                    boolean change = S[i].ClauseEvaluate(values);
                    if(change){//Clause is removed
                        S = ClauseRemoval(S[i].id, S);
                        i = 0; j = -1;
                    }
                    if(change == false && S[i].actual_clause.size()==0 && S.length == 1){//added
                        Clause[] badS = new Clause[1];
                        badS[0] = null;
                        return badS;
                    }
                    if(!change) {//didn't remove the clause, but clause might have changed
                        S[i].modify(values[j]);
                    } 
                }
                if(S[i].actual_clause.isEmpty()){
                    S = ClauseRemoval(S[i].id, S);
                }
            }
            return S;
        }
        // WORKS
        public Clause[] ClauseRemoval(int id, Clause[] S){
            boolean skipped = false;
            Clause[] newS = new Clause[S.length - 1];
            for(int i=0; i < S.length; i++){
                if(S[i].id == id){
                    //Skip this one
                    skipped = true;
                }
                else {
                    if(skipped){
                        newS[i-1] = S[i];
                    }
                    else {
                        newS[i] = S[i];
                    }
                }
            }
            return newS;
        }
        //Working
        public Data containsSingleSign(Clause[] S, Specialized_Integer[] V){//TODO
            boolean part = false; int indexFound = -1;
            Specialized_Integer outerATOM = null;
            HashMap<Integer, Boolean> seen = new HashMap();

            for(int i=0; i < S.length; i++){ 
                Specialized_Integer signATOM = null;
                int conflict = 0;
                HashMap<Integer, Specialized_Integer> clause = S[i].actual_clause;
                Set <Integer> setATOMs = clause.keySet();
                Integer[] ATOMs = new Integer[setATOMs.size()];
                ATOMs = setATOMs.toArray(ATOMs);
                for(int j = 0; j < ATOMs.length; j++){
                    Specialized_Integer iteration = clause.get(ATOMs[j]);
                    if(seen.containsKey(iteration.Atom)){//already know that it can't be this value
                        continue;
                    }
                    if(outerATOM != null && iteration.Atom != outerATOM.Atom){//different than outerATOM
                        continue;
                    }
                    if(outerATOM != null){
                    if(outerATOM.Atom == iteration.Atom && outerATOM.state != iteration.state){//outer mismatch
                        seen.put(outerATOM.Atom, outerATOM.state);
                        outerATOM = null;
                        signATOM = null;
                        indexFound = -1;
                        i = -1;
                        break;
                    }   }
                    //here OuterATOM is null so either its the first run or the last outerATOM was nullified
                    if(signATOM == null && outerATOM == null){
                        signATOM = iteration;
                        indexFound = findInV(iteration.Atom, V);
                        part = iteration.state;
                        continue;
                    }
                    else{
                    if(signATOM != null){
                    if(signATOM.Atom == iteration.Atom && signATOM.state != iteration.state){//inner mismatch
                        seen.put(signATOM.Atom, signATOM.state);
                        outerATOM = null;
                        signATOM = null;
                        indexFound = -1;
                    }   }   }
                }//end of inner forloop
                if(signATOM != null){
                outerATOM = signATOM;}
            }//end of outer forloop
            return new Data(part, indexFound);
        }
        //WORKS
        public int findInV(int Atom, Specialized_Integer[] V){
            for(int i=0; i<V.length; i++){
                if(V[i].Atom == Atom){
                    return i;
                }
            }
            return -1;//error
        }
        //Working
        public Data containsSingleConditional(Clause[] S, Specialized_Integer[] V){//TODO
            boolean part = false; int indexFound = -1;
            Specialized_Integer singleATOM;
            for(int i=0; i <  S.length; i++){
                HashMap<Integer, Specialized_Integer> clause = S[i].actual_clause;
                if(clause.size() == 1){//Only 1 atoms exist within that clause
                    Set <Integer> setATOMs = clause.keySet();
                    Integer[] ATOMs = new Integer[setATOMs.size()];
                    ATOMs = setATOMs.toArray(ATOMs);
                    singleATOM = clause.get(ATOMs[0]);
                    part = singleATOM.state; //Assuming that the state is set when parsering the String
                    indexFound = findInV(singleATOM.Atom, V);
                    break;
                }
                else {
                boolean debugger = true;} //multiple atoms don't evulate 
            }
            return new Data(part, indexFound);
        }
        private class Data{
            public int foundAt;
            public boolean shouldBe;
            
            public Data(boolean part1, int part2){
                shouldBe = part1;
                foundAt = part2;
            }
        }
        //WORKS
        public int evaluationClauses(Specialized_Integer[] V, Clause[] S){
            if(S == null){
                return 1;
            }
            if(S.length == 0){
                return 1; //No clauses left; contains a null
            }
            if(S.length == 1 && S[0] == null){//added
                return -1;
            }
            if(S.length == 1 && S[0].actual_clause.size() == 0) {
                return 1;//contradiction as there is no way of evulating the Clause
            }
            Specialized_Integer[] iteratedV = V;
            for(int i=0; i< S.length; i++){
                Clause tempC = S[i];
                boolean eval  = tempC.ClauseEvaluate(V);
                if(eval && S.length==1){//added
                    return -1;
                }
                if(eval){
                    if(tempC.evaluation == true){
                        //Clause has no problem
                        boolean debugger = true;
                    }
                    else {//Clause is null
                        return -1;
                    }   
                }
                else { //no evalation 
                    return 0;
                }
            }//Good eval
            return 1;
        }
        //prints out finalized V
        public void printV(){
            for(int Int=0;Int < final_V.length; Int++){
                System.out.println(final_V[Int].Atom + " " + final_V[Int].state);
            }
        }
    }

    public class Clause{
        public int id;
        public String passed_Clause;
        public HashMap<Integer, Specialized_Integer> actual_clause;
        public boolean evaluation;
        public boolean successEvaluated;
        
        public Clause(String line, int id){
            this.id = id;
            passed_Clause = line;
            actual_clause = ClauseParser(line);
            evaluation = false; //WARNING this is set to arbitally false
            successEvaluated = false;
            
        }
        // WORKS
        public boolean ClauseEvaluate(Specialized_Integer[] V){
            for(int i=0; i < V.length; i++){
                Integer reference = V[i].Atom;
                Specialized_Integer fromV = V[i];
                if(fromV.hasSet == false){
                    continue;
                }
                Specialized_Integer conditional = this.actual_clause.get(reference);
                if(conditional != null){//Found the part of the clause to be removed
                    if(conditional.state == fromV.state){
                       evaluation = true;//set to True
                       return true;
                    }
                    else { 
                    boolean debugger = true;} // No match
                }
                else {
                boolean debugger = true;} // Clause didn't exist
            }
            return false;
        }
        // WORKS
        public HashMap<Integer, Specialized_Integer> ClauseParser(String line){
            HashMap<Integer, Specialized_Integer> tempMap = new HashMap<>();
            boolean negated = false; Integer toInt = new Integer(-1);
            String collectingDigits = "";
            for(int index=0; index < line.length(); index++){
                if(line.charAt(index) == '-'){
                    negated = true;
                }
                if( isNumeric(line.charAt(index)) ){
                    collectingDigits = collectingDigits + line.substring(index, index+1);
                }
                if(line.charAt(index) == ' '){
                    if(collectingDigits != "" && collectingDigits != null){
                        toInt = Integer.parseInt(collectingDigits);
                        Specialized_Integer ATOM = new Specialized_Integer(toInt);
                        if(negated){
                            ATOM.state = false; ATOM.hasSet = true;
                            tempMap.put(toInt, ATOM);
                            negated = false;
                        }
                        else {
                            ATOM.state = true; ATOM.hasSet = true;
                            tempMap.put(toInt, ATOM); 
                        }
                        collectingDigits = "";
                    }
                }
            }
            //printHashMap(tempMap, this.id);
            return tempMap;
        }
        //WORKS
        public void printHashMap(HashMap<Integer, Specialized_Integer> map, int iter){
        Set<Integer> set = map.keySet();
        Integer[] keyList = {};
        keyList = set.toArray(keyList);
        
        System.out.println("This is the HashMap, Clause with id of " + iter + " and with the ATOMs: ");
        for(int index = 0; index < set.size(); index++){
            Integer key = keyList[index];
            if(map.get(key) != null){
            System.out.println("Key: " + key + "; Value: " + 
                    map.get(key).toString());
            }
            else {
                System.out.println("null");
            }
        }
    }
        public boolean isNumeric(char Char){
            if(Char == '1' || Char == '2' || Char == '3'){
                return true;
            }
            if(Char == '4' || Char == '5' || Char == '6'){
                return true;
            }
            if(Char == '7' || Char == '8' || Char == '9'){
                return true;
            }
            return false;
        }
        // WORKS
        public void modify(Specialized_Integer ATOM){
           Integer reference = (ATOM.Atom);
           Specialized_Integer conditional = this.actual_clause.get(reference.intValue());
           if(conditional != null){//Found the part of the clause to be removed
                if(conditional.state != ATOM.state){
                   this.actual_clause.remove(reference);//removed because there should be a mismatch with the ATOMs
                }
                else {
                    this.evaluation = true; //should not happen but in case it does ?? Maybe move to Parser??
                }
           }
        }
    }
    
    public class Specialized_Integer{
        boolean state;
        boolean hasSet;
        int occurances;
        int negated_occurances;
        int Atom;
        
        public Specialized_Integer(int input){
            Atom = input;
            occurances = 0;
            negated_occurances = 0;
            state = false;//Warning this set to false arbitally
            hasSet = false;
        }
        public void changeState(boolean change){
            state = change;
            hasSet = true;
        }
        public void incrementOccurances(int amount, boolean which){
            for(int i=0; i< amount; i++){
                if(which){//regular
                    occurances++;
                }
                else {//negated
                    negated_occurances++;
                }
            }
        }
        public void decrementOccurances(int amount, boolean which){
            for(int i=0; i< amount; i++){
                if(which){//regular
                    if(occurances==0){}
                    else { occurances--; }
                }
                else {//negated
                    if(negated_occurances==0){}
                    else { negated_occurances--; }
                }
            }
        }
        @Override
        public String toString(){
            return "This ATOMs is " + this.Atom + " with the state of " + this.state;
        }
    }
}