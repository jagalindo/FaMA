package es.us.isa.Choco.fmdiag.configuration;

import static choco.Choco.eq;

import java.lang.management.ThreadInfo;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.concurrent.Callable;
import java.util.concurrent.CompletionService;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorCompletionService;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.ForkJoinPool;
import java.util.concurrent.Future;
import java.util.concurrent.RecursiveTask;

import choco.Choco;
import choco.cp.model.CPModel;
import choco.cp.solver.CPSolver;
import choco.kernel.model.Model;
import choco.kernel.model.constraints.Constraint;
import choco.kernel.model.variables.integer.IntegerExpressionVariable;
import choco.kernel.model.variables.integer.IntegerVariable;
import choco.kernel.solver.Solver;
import es.us.isa.ChocoReasoner.ChocoQuestion;
import es.us.isa.ChocoReasoner.ChocoReasoner;
import es.us.isa.ChocoReasoner.ChocoResult;
import es.us.isa.FAMA.Benchmarking.PerformanceResult;
import es.us.isa.FAMA.Exceptions.FAMAException;
import es.us.isa.FAMA.Reasoner.Reasoner;
import es.us.isa.FAMA.Reasoner.questions.ExplainErrorsQuestion;
import es.us.isa.FAMA.Reasoner.questions.ValidConfigurationErrorsQuestion;
import es.us.isa.FAMA.errors.Error;
import es.us.isa.FAMA.errors.Observation;
import es.us.isa.FAMA.models.featureModel.GenericFeature;
import es.us.isa.FAMA.models.featureModel.Product;
import es.us.isa.FAMA.models.variabilityModel.VariabilityElement;
import es.us.isa.FAMA.stagedConfigManager.Configuration;

import java.util.Arrays;
import java.util.Collections;

public class ChocoExplainErrorFMDIAGParalell extends ChocoQuestion implements ValidConfigurationErrorsQuestion {

	public boolean returnAllPossibeExplanations = false;
	private ChocoReasoner chReasoner;

	Map<String, Constraint> relations = null;
	public boolean flexactive = false;
	public int m = 1;

	Product s,r;
	public Map<String, Constraint> result = new HashMap<String, Constraint>();

	public void setConfiguration(Product s) {
		this.s=s;
	}

	public void setRequirement(Product r) {
		this.r=r;
	}
	
	
	public int numberOfThreads = 4;
	public int baseSize = 100;

	//public ExecutorService executorService = Executors.newCachedThreadPool();
	public ExecutorService executorService;
	////////////For Parallel FlexDiag...
	
	public ChocoExplainErrorFMDIAGParalell(int m, int t){
		this.m = m;
		this.numberOfThreads = t;

		//executorService = Executors.newFixedThreadPool(2);
	}
	
	//

	public PerformanceResult answer(Reasoner r) throws FAMAException {
		chReasoner = (ChocoReasoner) r;
		// solve the problem y fmdiag
		relations = new HashMap<String, Constraint>();

		Map<String, Constraint> productConstraint = new HashMap<String, Constraint>();
		ArrayList<String> feats= new ArrayList<String>();
		for (GenericFeature f : this.s.getFeatures()) {
			IntegerVariable var = chReasoner.getVariables().get(f.getName());
			//System.out.println(var);
			String name="U_" + f.getName();
			productConstraint.put(name, Choco.eq(var, 0));
			feats.add(name);
		}

		Map<String, Constraint> requirementConstraint = new HashMap<String, Constraint>();
		for (GenericFeature f : this.r.getFeatures()) {
			IntegerVariable var = chReasoner.getVariables().get(f.getName());
			//System.out.println(var);
			requirementConstraint.put("R_" + f.getName(), Choco.eq(var, 1));
		}

		relations.putAll(chReasoner.getRelations());
		relations.putAll(requirementConstraint);
		relations.putAll(productConstraint);
		ArrayList<String> S = new ArrayList<String>(feats);
		//System.out.println("Order of S: "+S);
		ArrayList<String> AC = new ArrayList<String>(relations.keySet());
		//AC.addAll(productConstraint.keySet());

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

		return new ChocoResult();
	}
	
	private List<String> plus(List<String> a1, List<String> a2) {
		List<String> res = new ArrayList<String>();
		res.addAll(a1);
		res.addAll(a2);
		return res;
	}

	public List<String> fmdiag(List<String> S, List<String> AC) {
		//S is empty or (AC - S) non-consistent
		if (S.size() == 0 || !isConsistent(less(AC, S))) {
			return new ArrayList<String>();
		} 
		else { 		
			//(AC + S) is non-consistent
			ForkJoinPool pool = new ForkJoinPool();
			diagThreadsFJ dt = new diagThreadsFJ(new ArrayList<String>(), S, AC, numberOfThreads, executorService);
			List<String> solution = pool.invoke(dt);
			return solution;
		}
	}

	public class diagThreadsFJ extends RecursiveTask<List<String>>{
		List<String> D, S, AC;
		int numberOfSplits;
		ExecutorService executorService;
		
			public diagThreadsFJ(List<String> D, List<String> S,List<String> AC,int numberOfSplits, ExecutorService executorService){
			this.D=D;
			this.S=S;
			this.AC=AC;
			this.executorService=executorService;
			this.numberOfSplits=numberOfSplits;	
		}
		
		/*Each thread (instance of this class) presents values for its attributes D, S, and AC. 
		 *(D + S) represents the set of rules to analyze; D and S are complementary, and S 
		 *corresponds to the current solution set.
		 *
		 *At the start point of the call() method , always:
		 *	- S represents the solution set.
		 *	- D represents the complement set of S concerning the previous solution set.
		 *	- AC represents the consistent rules of model C + the rules of S.  
		 *
		 *For the 1st thread always D is empty and S inconsistent. Then, AC is inconsistent.*/
		
		public List<String> compute(){		
		/*1st base case*/
			if (D.size() != 0 && isConsistent(AC)){	
				/*Since AC does not contain D, when D is not empty and AC is consistent, 
				 *then D contains inconsistencies then D is analyzed to look for them*/
				return new ArrayList<String>();
			}
			
		/*Since AC is non-consistent and D is not the inconsistencies source, then S is their source.
		 *If this algorithmic solution is 'flexible' and the size of S is lesser or equal than m, then 
		 *S is the looked inconsistencies set (m defines the solution flexibility to 
		 *contains some consistent rules). 
		 *
		 *If this solution is not 'flexible' and S contains only one rule, then S is the looked inconsistent set*/
			
		/*2nd base case*/
			if(flexactive){
				if(S.size()<=m){
				   return S;
				}
			}else{				
				if(S.size()==1){
				   return S;
				}
			}
			
		/*outList corresponds to a results list for the threads of the solution*/
			List<List<String>> outLists= new LinkedList<List<String>>();
		
			////*DIVISION PHASE*////
			int div = 0; //div is the size of the partitions
						
			if (S.size() >= numberOfSplits){
			   div = S.size() / numberOfSplits;
			   if ((S.size() % numberOfSplits)>0)
				   div++;
			}
			else 
				div = 1;
			
			List<List<String>> splitListToSubLists = splitListToSubLists(S, div);
			int actDiv = 0, maxDiv = splitListToSubLists.size();
			
			List<RecursiveTask<List<String>>> forks = new ArrayList<>();
						
			////*CONQUER PHASE*////
			for(List<String> s: splitListToSubLists){
				/*For each partition 's', we define its complement 'rest' (AC - s) and  
				 *the rules set 'less' (AC - rest). 
				 *Then, a new thread 'dt' is defined with D=rest, S=s, and AC=less, 'dt' is run,
				 *and its results are grouped in the results list*/ 		
				if (actDiv == (maxDiv-1))
					break;

				List<String> rest= getRest(s,splitListToSubLists);	
				List<String> less = less(AC,rest);
				
				diagThreadsFJ dt = new diagThreadsFJ(rest, s,less , numberOfSplits, executorService);
				dt.fork();
				
				forks.add(dt);
				
				if (actDiv < (maxDiv-1))
					actDiv++;
			}

			for(RecursiveTask<List<String>> subTask: forks){
		       outLists.add(subTask.join());						
			}
			
			/*We save and return the union of the results of lists*/
			List<String> fullSolution1 = plus(outLists);
			
			/*FMDiag 2nd call*/
			List<String> s = splitListToSubLists.get(actDiv);
			List<String> less = less(AC,fullSolution1);
			
			diagThreadsFJ dt = new diagThreadsFJ(fullSolution1, s,less , numberOfSplits, executorService);
			dt.fork();
			
			outLists.add(dt.join());						
	    	List<String> fullSolution = plus(outLists);
			
			return fullSolution;
		}
		
		private List<String> getRest(List<String> s2, List<List<String>> splitListToSubLists) {
			try{
				LinkedList<String> res= new LinkedList<String>();
				for(List<String> c:splitListToSubLists){
					if(c!=s2){
						res.addAll(c);
					}
				}
				return res;
			}catch(Exception ex){ 
				System.out.println(ex.getMessage());
				return null;
			}

		}

		private List<String> plus(List<List<String>> outLists) {
			try{
				List<String> res=new ArrayList<String>();
				for(List<String> s:outLists){	
					res.addAll(s);
				}
				return res;
			}catch(Exception ex){ 
				System.out.println(ex.getMessage());
				return null;
			}

		}

		public <T> List<List<T>> splitListToSubLists(List<T> parentList, int subListSize) {
			try{
			 List<List<T>> subLists = new ArrayList<List<T>>();
			  
			  if (subListSize > parentList.size()) {
			     subLists.add(parentList);
			     } 
			  else {
			     int remainingElements = parentList.size();
			     int startIndex = 0;
			     int endIndex = subListSize;
			     do {
			        List<T> subList = parentList.subList(startIndex, endIndex);
			        subLists.add(subList);
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
			}catch(Exception ex){ 
				System.out.println(ex.getMessage());
				return null;
			}
			
		}
   }
	
	public class diagThreads implements Callable<List<String>>{
		List<String> D, S, AC;
		int numberOfSplits;
		ExecutorService executorService;
				
		public diagThreads(List<String> D, List<String> S,List<String> AC,int numberOfSplits, ExecutorService executorService){
			this.D=D;
			this.S=S;
			this.AC=AC;
			this.executorService=executorService;
			this.numberOfSplits=numberOfSplits;	
		}
		
		/*Each thread (instance of this class) presents values for its attributes D, S, and AC. 
		 *(D + S) represents the set of rules to analyze; D and S are complementary, and S 
		 *corresponds to the current solution set.
		 *
		 *At the start point of the call() method , always:
		 *	- S represents the solution set.
		 *	- D represents the complement set of S concerning the previous solution set.
		 *	- AC represents the consistent rules of model C + the rules of S.  
		 *
		 *For the 1st thread always D is empty and S inconsistent. Then, AC is inconsistent.*/
		
		public List<String> call() throws Exception {		
		/*1st base case*/
			if (D.size() != 0 && isConsistent(AC)){	
				/*Since AC does not contain D, when D is not empty and AC is consistent, 
				 *then D contains inconsistencies then D is analyzed to look for them*/
				return new ArrayList<String>();
			}
			
		/*Since AC is non-consistent and D is not the inconsistencies source, then S is their source.
		 *If this algorithmic solution is 'flexible' and the size of S is lesser or equal than m, then 
		 *S is the looked inconsistencies set (m defines the solution flexibility to 
		 *contains some consistent rules). 
		 *
		 *If this solution is not 'flexible' and S contains only one rule, then S is the looked inconsistent set*/
			
		/*2nd base case*/
			if(flexactive){
				if(S.size()<=m){
				   return S;
				}
			}else{				
				if(S.size()==1){
				   return S;
				}
			}
			
		/*outList corresponds to a results list for the threads of the solution*/
			List<List<String>> outLists= new LinkedList<List<String>>();
		
			////*DIVISION PHASE*////
			int div = 0; //div is the size of the partitions
						
			if (S.size() >= numberOfSplits){
			   div = S.size() / numberOfSplits;
			   if ((S.size() % numberOfSplits)>0)
				   div++;
			}
			else 
				div = 1;
			
			List<List<String>> splitListToSubLists = splitListToSubLists(S, div);
			int actDiv = 0, maxDiv = splitListToSubLists.size();
			
			List<Future<List<String>>> submit = new ArrayList<Future<List<String>>>();
						
			///////////////////*******////////////////////////
			/////ExecutorService threadPool = Executors.newFixedThreadPool(numberOfThreads);
			//CompletionService<List<String>> pool = new ExecutorCompletionService<List<String>>(executorService);
			//////////////////*******/////////////////////////
			
			////*CONQUER PHASE*////
			for(List<String> s: splitListToSubLists){
				/*For each partition 's', we define its complement 'rest' (AC - s) and  
				 *the rules set 'less' (AC - rest). 
				 *Then, a new thread 'dt' is defined with D=rest, S=s, and AC=less, 'dt' is run,
				 *and its results are grouped in the results list*/ 		
				if (actDiv == (maxDiv-1))
					break;

				List<String> rest= getRest(s,splitListToSubLists);	
				List<String> less = less(AC,rest);
				
				diagThreads dt = new diagThreads(rest, s,less , numberOfSplits, executorService);
				
				//Future<List<String>> submit = executorService.submit(dt);
				 submit.add(executorService.submit(dt));
				///Cambio 1: pool.submit(dt);
				
				
				if (actDiv < (maxDiv-1))
					actDiv++;
			}
			
			for(int i=0; i < actDiv; i++){
				outLists.add(submit.get(i).get());
				submit.get(i).cancel(true);
			}
			///Cambio 2: outLists.add(pool.take().get());
			
			/*We save and return the union of the results of lists*/
			List<String> fullSolution1 = plus(outLists);
			
			/*FMDiag 2nd call*/
			List<String> s = splitListToSubLists.get(actDiv);
			List<String> less = less(AC,fullSolution1);
			
			diagThreads dt = new diagThreads(fullSolution1, s,less , numberOfSplits, executorService);
			submit.add(executorService.submit(dt));
  		    /////Cambio 3:pool.submit(dt);
			
			outLists.add(submit.get(actDiv).get());		
	   	    ////Cambio 4: outLists.add(pool.take().get());
			submit.get(actDiv).cancel(true);
			
			List<String> fullSolution = plus(outLists);
			
			////Cambio 5:
			//threadPool.shutdown();
						
			return fullSolution;
		}
		
		private List<String> getRest(List<String> s2, List<List<String>> splitListToSubLists) {
			LinkedList<String> res= new LinkedList<String>();
			for(List<String> c:splitListToSubLists){
				if(c!=s2){
					res.addAll(c);
				}
			}
			return res;
		}

		private List<String> plus(List<String> a1, List<String> a2) {
			List<String> res = new ArrayList<String>();
			res.addAll(a1);
			res.addAll(a2);
			return res;
		}

		private List<String> plus(List<List<String>> outLists) {
			List<String> res=new ArrayList<String>();
			for(List<String> s:outLists){	
				res.addAll(s);
			}
			return res;		
		}

		public <T> List<List<T>> splitListToSubLists(List<T> parentList, int subListSize) {
			  List<List<T>> subLists = new ArrayList<List<T>>();
			  
			  if (subListSize > parentList.size()) {
			     subLists.add(parentList);
			     } 
			  else {
			     int remainingElements = parentList.size();
			     int startIndex = 0;
			     int endIndex = subListSize;
			     do {
			        List<T> subList = parentList.subList(startIndex, endIndex);
			        subLists.add(subList);
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
   }
	
	private List<String> less(List<String> aC, List<String> s2) {
		List<String> res = new ArrayList<String>();
		res.addAll(aC);
		res.removeAll(s2);
		return res;
	}

	private boolean isConsistent(Collection<String> aC) {
		Model p = new CPModel();
		p.addVariables(chReasoner.getVars());

		for (String rel : aC) {
			Constraint c = relations.get(rel);

			if (c == null) {
				System.out.println("Error");
			}
			p.addConstraint(c);
		}
		Solver s = new CPSolver();
		s.read(p);
		s.solve();
		return s.isFeasible();
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