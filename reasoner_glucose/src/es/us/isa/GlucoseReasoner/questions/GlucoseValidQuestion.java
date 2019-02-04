/*
	This file is part of FaMaTS.

    FaMaTS is free software: you can redistribute it and/or modify
    it under the terms of the GNU Lesser General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    FaMaTS is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU Lesser General Public License for more details.

    You should have received a copy of the GNU Lesser General Public License
    along with FaMaTS.  If not, see <http://www.gnu.org/licenses/>.

 */
package es.us.isa.GlucoseReasoner.questions;

import java.io.InputStream;

import es.us.isa.FAMA.Benchmarking.PerformanceResult;
import es.us.isa.FAMA.Exceptions.FAMAParameterException;
import es.us.isa.FAMA.Reasoner.Reasoner;
import es.us.isa.FAMA.Reasoner.questions.ValidQuestion;
import es.us.isa.GlucoseReasoner.GlucoseQuestion;
import es.us.isa.GlucoseReasoner.GlucoseReasoner;
import es.us.isa.GlucoseReasoner.GlucoseResult;

public class GlucoseValidQuestion extends GlucoseQuestion implements ValidQuestion {
	/**
	 * @uml.property  name="valid"
	 */
	private boolean valid;
	
	public GlucoseValidQuestion() {
		valid = false;
	}
	
	/**
	 * @return
	 * @uml.property  name="valid"
	 */
	public boolean isValid() {
		return valid;
	}
	
	// Answer the question
	public PerformanceResult answer(Reasoner r) {
		if(r==null){
			throw new FAMAParameterException("Reasoner :Not specified");
		}
		GlucoseResult res = new GlucoseResult();
		InputStream cnfFilePath = ((GlucoseReasoner) r).getStream();
		
		
		return res;
	}
	
	public String toString() {
		if (valid)
			return "Feature model is valid";
		else
			return "Feature model is not valid";
	}
}
