package es.us.isa.Sat4j.fmdiag;

import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.concurrent.CopyOnWriteArrayList;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.ForkJoinPool;
import java.util.concurrent.RecursiveTask;

import org.sat4j.minisat.SolverFactory;
import org.sat4j.reader.DimacsReader;
import org.sat4j.reader.ParseFormatException;
import org.sat4j.reader.Reader;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.TimeoutException;

import es.us.isa.FAMA.Benchmarking.PerformanceResult;
import es.us.isa.FAMA.Exceptions.FAMAException;
import es.us.isa.FAMA.Reasoner.Reasoner;
import es.us.isa.FAMA.Reasoner.questions.ValidConfigurationErrorsQuestion;
import es.us.isa.FAMA.models.featureModel.GenericFeature;
import es.us.isa.FAMA.models.featureModel.Product;
import es.us.isa.Sat4jReasoner.Sat4jQuestion;
import es.us.isa.Sat4jReasoner.Sat4jReasoner;
import es.us.isa.Sat4jReasoner.Sat4jResult;

public class Sat4jExplainErrorFMDIAGParalell extends Sat4jQuestion implements ValidConfigurationErrorsQuestion {

	public boolean returnAllPossibeExplanations = false;
	public Map<String, String> result = new HashMap<String, String>();

	Map<String, String> relations = null;
	public boolean flexactive = false;
	public int m = 1;
	private Sat4jReasoner reasoner;

	Product s, r;
	//public Map<String, Constraint> result = new HashMap<String, Constraint>();

	public void setConfiguration(Product s) {
		this.s = s;
	}

	public void setRequirement(Product r) {
		this.r = r;
	}

	public int numberOfThreads = 4;
	public int baseSize = 100;

	public ExecutorService executorService;

	public Sat4jExplainErrorFMDIAGParalell(int m, int t) {
	  this.m = m;
    this.numberOfThreads = t;
	}
	
	public PerformanceResult answer(Reasoner r) throws FAMAException {
		reasoner = (Sat4jReasoner) r;
		// solve the problem y fmdiag
		relations = new HashMap<String, String>();

		Map<String, String> productConstraint = new HashMap<String, String>();
		ArrayList<String> feats = new ArrayList<String>();
		for (GenericFeature f : this.s.getFeatures()) {
			String cnfVar = reasoner.getCNFVar(f.getName());
			String name = "U_" + f.getName();
			productConstraint.put(name, "-"+cnfVar+" 0");
			feats.add(name);
		}

		Map<String, String> requirementConstraint = new HashMap<String, String>();
		for (GenericFeature f : this.r.getFeatures()) {
			String cnfVar = reasoner.getCNFVar(f.getName());
			requirementConstraint.put("R_" + f.getName(), cnfVar+" 0");
		}

		int cindex= 0;
		for(String cl:reasoner.clauses){
			relations.put(cindex+"rel", cl);
		}
		relations.putAll(requirementConstraint);
		relations.putAll(productConstraint);

		//The use of this class is to force synced lists
		CopyOnWriteArrayList<String> S = new CopyOnWriteArrayList<String>(feats);
		CopyOnWriteArrayList<String> AC = new CopyOnWriteArrayList<String>(relations.keySet());

		if (returnAllPossibeExplanations == false) {

			List<String> fmdiag = fmdiag(S, AC);

			for (String s : fmdiag) {
				result.put(s, productConstraint.get(s));
			}

		} else {
			List<String> allExpl = new LinkedList<String>();
			List<String> fmdiag = fmdiag(S, AC);

			while (fmdiag.size() != 0) {
				allExpl.addAll(fmdiag);
				S.removeAll(fmdiag);
				AC.removeAll(fmdiag);
				fmdiag = fmdiag(S, AC);
			}
			for (String s : allExpl) {
				result.put(s, productConstraint.get(s));
			}
		}

		return new Sat4jResult();
	}

	public CopyOnWriteArrayList<String> fmdiag(CopyOnWriteArrayList<String> S, CopyOnWriteArrayList<String> AC) {		// S is empty or (AC - S) non-consistent
		// S is empty or (AC - S) non-consistent
		if (S.size() == 0 || !isConsistent(less(AC, S))) {
			return new CopyOnWriteArrayList<String>();
		} else {
			// (AC + S) is non-consistent
			ForkJoinPool pool = new ForkJoinPool(numberOfThreads);
			diagThreadsFJ dt = new diagThreadsFJ(new CopyOnWriteArrayList<String>(), S, AC, numberOfThreads);
		    dt.type = 1; dt.res=-1;
		    
			CopyOnWriteArrayList<String> solution = pool.invoke(dt);
			return solution;
		}
	}

	
	private CopyOnWriteArrayList<String> less(CopyOnWriteArrayList<String> aC, CopyOnWriteArrayList<String> s2) {
		CopyOnWriteArrayList<String> res = new CopyOnWriteArrayList<String>();
		res.addAll(aC);
		res.removeAll(s2);
		return res;
	}
	
	public class diagThreadsFJ extends RecursiveTask<CopyOnWriteArrayList<String>> {
		private static final long serialVersionUID = 1L;
		
		CopyOnWriteArrayList<String> D, S, AC;
		int numberOfSplits;

		
		Integer type; 
		/*type 1 = main thread that can create other threads

    type 2 = thread to review base cases only
		*/
				
		Integer res; 
		/*res 1 = base case 1
		  res 2 = base case 2
		  res 2 = no solution (type 2 thread)
		*/
		

		public diagThreadsFJ(CopyOnWriteArrayList<String> D, CopyOnWriteArrayList<String> S,
				CopyOnWriteArrayList<String> AC, int numberOfSplits) {
			this.D = D;
			this.S = S;
			this.AC = AC;
			this.numberOfSplits = numberOfSplits;

		}

		/*
		 * Each thread (instance of this class) presents values for its attributes D, S,
		 * and AC. (D + S) represents the set of rules to analyze; D and S are
		 * complementary, and S corresponds to the current solution set.
		 *
		 * At the start point of the call() method , always: - S represents the solution
		 * set. - D represents the complement set of S concerning the previous solution
		 * set. - AC represents the consistent rules of model C + the rules of S.
		 *
		 * For the 1st thread always D is empty and S inconsistent. Then, AC is
		 * inconsistent.
		 */

		public CopyOnWriteArrayList<String> compute() {
			/* 1st base case */
			if (D.size() != 0 && isConsistent(AC)) {
				/*
				 * Since AC does not contain D, when D is not empty and AC is consistent, then D
				 * contains inconsistencies then D is analyzed to look for them
				 */
				this.res = 1;

				return new CopyOnWriteArrayList<String>();
			}

			/*
			 * Since AC is non-consistent and D is not the inconsistencies source, then S is
			 * their source. If this algorithmic solution is 'flexible' and the size of S is
			 * lesser or equal than m, then S is the looked inconsistencies set (m defines
			 * the solution flexibility to contains some consistent rules).
			 *
			 * If this solution is not 'flexible' and S contains only one rule, then S is
			 * the looked inconsistent set
			 */

			/* 2nd base case */
			if (flexactive) {
				if (S.size() <= m) {
					this.res = 2;

					return S;
				}
			} else {
				if (S.size() == 1) {
					this.res = 2;

					return S;
				}
			}

			if (this.type==2){ /*3rdbase case - type 2 and no solution*/
				this.res=3;
				return new CopyOnWriteArrayList<String>();
			}

			/* outList corresponds to a results list for the threads of the solution */
			CopyOnWriteArrayList<CopyOnWriteArrayList<String>> outLists = new CopyOnWriteArrayList<CopyOnWriteArrayList<String>>();

			//// *DIVISION PHASE*////
			int div = 0; // div is the size of the partitions

			if (S.size() >= numberOfSplits) {
				div = S.size() / numberOfSplits;
				if ((S.size() % numberOfSplits) > 0) {
					div++;
				}
			} else
				div = 1;

			CopyOnWriteArrayList<CopyOnWriteArrayList<String>> splitListToSubLists = splitListToSubLists(S, div);
			CopyOnWriteArrayList<RecursiveTask<CopyOnWriteArrayList<String>>> forks = new CopyOnWriteArrayList<>();

			////*CONQUER PHASE*////		
			CopyOnWriteArrayList<CopyOnWriteArrayList<String>> rest = new CopyOnWriteArrayList<CopyOnWriteArrayList<String>>();
			CopyOnWriteArrayList<CopyOnWriteArrayList<String>> less = new CopyOnWriteArrayList<CopyOnWriteArrayList<String>>();
			CopyOnWriteArrayList<diagThreadsFJ> threads = new CopyOnWriteArrayList<diagThreadsFJ>();	
			
			int j=0;
			for(int i = splitListToSubLists.size()-1; i>=0; i--){
				CopyOnWriteArrayList<String> s = splitListToSubLists.get(i);	//S	
				/*
				 * For each partition 's', we define its complement 'rest' (AC - s) and the
				 * rules set 'less' (AC - s). Then, a new thread 'dt' is defined with D = s,
				 * S = rest, and AC = less, 'dt' is run, and its results are grouped in the results
				 * list
				 */
				rest.add(getRest(s,splitListToSubLists));	//D
				less.add(less(AC,s));
				
				/*a new thread to define if it can directly find the preferred inconsistency*/

        diagThreadsFJ dt = new diagThreadsFJ(s, rest.get(j), less.get(j) , this.numberOfSplits); 
				dt.type = 2; 
				threads.add(dt);
				
				dt.fork();
				forks.add(dt);
				j++;
			}

			/*The results are take for each created thread!
			 looking for the preferred diagnosis. 
			 If some thread found a diagnosis(they are obtained in a preferred order),
			 that thread is the winner (siblings and nephews threads possibly return)..*/
			int i=0; Boolean sw=false; Integer posZero=-1;

			for(RecursiveTask<CopyOnWriteArrayList<String>> subTask: forks){
				CopyOnWriteArrayList<String> rr = subTask.join();
				
				if (rr.size()>=0 && !sw && threads.get(i).res != 3){ //thread found a 'base case', i.e., that thread can find or found a solution  
					outLists.add(rr);
					if (rr.size() > 0 && posZero==-1){ //if that thread is the first discovering a solution 
						posZero = -1; sw=true; //thread is the winner
					}else if (posZero==-1)
						posZero=i;
				}
				
				i++;
			}

			//if no thread directly found a solution, we choose the one that work on the preferred set for diagnosis 
			if (posZero != -1){
				/*FMDiag 2nd call*/
				CopyOnWriteArrayList<String> s = splitListToSubLists.get(splitListToSubLists.size()-1-posZero);
				CopyOnWriteArrayList<String> acc = less(AC, outLists.get(posZero));
				diagThreadsFJ dt = new diagThreadsFJ(outLists.get(posZero), s, acc, numberOfSplits);
				dt.type = 1;  
						
				dt.fork();
				outLists.add(dt.join());						
			}
			
			CopyOnWriteArrayList<String> fullSolution = plus(outLists);

			return fullSolution;
		}

		private CopyOnWriteArrayList<String> getRest(CopyOnWriteArrayList<String> s2,
				CopyOnWriteArrayList<CopyOnWriteArrayList<String>> splitListToSubLists) {
			CopyOnWriteArrayList<String> res = new CopyOnWriteArrayList<String>();

			for (CopyOnWriteArrayList<String> c : splitListToSubLists) {
				if (c != s2) {
					res.addAll(c);
				}
			}
			return res;
		}

		private CopyOnWriteArrayList<String> plus(CopyOnWriteArrayList<CopyOnWriteArrayList<String>> outLists) {
			CopyOnWriteArrayList<String> res = new CopyOnWriteArrayList<String>();
			for (List<String> s : outLists) {
				res.addAll(s);
			}
			return res;
		}

		public <T> CopyOnWriteArrayList<CopyOnWriteArrayList<T>> splitListToSubLists(CopyOnWriteArrayList<T> parentList,
				int subListSize) {

			CopyOnWriteArrayList<CopyOnWriteArrayList<T>> subLists = new CopyOnWriteArrayList<CopyOnWriteArrayList<T>>();

			if (subListSize > parentList.size()) {
				subLists.add(parentList);
			} else {
				int remainingElements = parentList.size();
				int startIndex = 0;
				int endIndex = subListSize;
				do {
					List<T> subList = parentList.subList(startIndex, endIndex);
					subLists.add(new CopyOnWriteArrayList<T>(subList));
					startIndex = endIndex;
					if (remainingElements - subListSize >= subListSize) {
						endIndex = startIndex + subListSize;
					} else {
						endIndex = startIndex + remainingElements - subList.size();
					}
					remainingElements -= subList.size();
				} while (remainingElements > 0);

			}
			return subLists;
		}
		
		private CopyOnWriteArrayList<String> less(CopyOnWriteArrayList<String> aC, CopyOnWriteArrayList<String> s2) {
			CopyOnWriteArrayList<String> res = new CopyOnWriteArrayList<String>();
			res.addAll(aC);
			res.removeAll(s2);
			return res;
		}
		
	}

	private boolean isConsistent(Collection<String> aC) {
   		
		//First we create the content of the cnf
		String cnf_content = "c CNF file\n";

		// We show as comments the variables's number
		Iterator<String> it = reasoner.variables.keySet().iterator();
		while (it.hasNext()) {
			String varName = it.next();
			cnf_content += "c var " + reasoner.variables.get(varName) + " = " + varName
					+ "\n";
		}

		// Start the problem
		cnf_content += "p cnf " + reasoner.variables.size() + " " +  relations.values().size()
				+ "\n";
		// Clauses
		it = relations.values().iterator();
		while (it.hasNext()) {
			cnf_content += (String) it.next() + "\n";
		}

		// End file
		cnf_content += "0";
		ByteArrayInputStream stream= new ByteArrayInputStream(cnf_content.getBytes(StandardCharsets.UTF_8));
		
		
		
		ISolver s = SolverFactory.newDefault();
		Reader reader = new DimacsReader(s);
		try {
			reader.parseInstance(stream);
			return s.isSatisfiable();
		} catch (TimeoutException | ParseFormatException | ContradictionException | IOException e) {
			e.printStackTrace();
			
		}
		return false;
	}
	
		@Override
	public void setProduct(Product p) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public boolean isValid() {
		// TODO Auto-generated method stub
		return false;
	}

}