<Query Kind="Program">
  <Reference>&lt;RuntimeDirectory&gt;\System.ValueTuple.dll</Reference>
  <NuGetReference Version="2.2.3">UltraDES</NuGetReference>
  <Namespace>System</Namespace>
  <Namespace>System.Collections.Generic</Namespace>
  <Namespace>System.Linq</Namespace>
  <Namespace>UltraDES</Namespace>
</Query>

enum EventType
	{
		legitimate = 0,
		pC = 1,
		mC = 2,
		pN = 3,
		mN = 4
	}

public static void Main()
{
	var s = Enumerable.Range(0, 6).Select(i => new State($"s{i}", i == 0 ? Marking.Marked : Marking.Unmarked)).ToArray();
	//var e = Enumerable.Range(0, 100).Select(i => new Event($"e{i}", i % 2 != 0 ? Controllability.Controllable : Controllability.Uncontrollable)).ToArray();


	Event a1 = new Event("a1", Controllability.Controllable);
	Event b1 = new Event("b1", Controllability.Uncontrollable);
	Event a2 = new Event("a2", Controllability.Controllable);
	Event b2 = new Event("b2", Controllability.Uncontrollable);


	var G1 = new DeterministicFiniteAutomaton(
	new[]
	{
		new Transition(s[0], a1, s[1]),
		new Transition(s[1], b1, s[0])
	},
	s[0], "G1");

	var G2 = new DeterministicFiniteAutomaton(
	new[]
	{
		new Transition(s[0], a2, s[1]),
		new Transition(s[1], b2, s[0])
	},
	s[0], "G2");

	var E1 = new DeterministicFiniteAutomaton(
		new[]
		{
			new Transition(s[0], a1, s[3]),
			new Transition(s[3], b1, s[4]),
			new Transition(s[4], a2, s[1]),
			new Transition(s[1], b2, s[0]),
			new Transition(s[1], a1, s[2]),
			new Transition(s[2], b1, s[5]),
			new Transition(s[5], b2, s[4]),
			new Transition(s[2], b2, s[3]),
		},
		s[0], "E1");

	List<Event> EAC = new List<Event>() { a1 };
	List<Event> EAuC = new List<Event>() { b1 };
	
	SpecificationEstimator(out var TE, E1, EAC, EAuC);

	ControllerEstimator(out var TG, G1);
	//NetworkEstimator(out var TN, G1);

	//var ThetaG = TG.ParallelCompositionWith(TN);
	//ThetaG.ShowAutomaton("Theta");

	/*
	TO DO:
	- Testar o algoritmo. Fazer um conjunto de autômatos para serem testados.
	- Modificar o algoritmo no texto.
	- Atualizar a prova, tirando a parte de que a especificação tem que ser controlável.
	*/
}

static void SpecificationEstimator(out DeterministicFiniteAutomaton ThetaE, DeterministicFiniteAutomaton E, List<Event> EAC, List<Event> EAuC)
{
	//var events = new Ev //row: type of event; column: event
	List<Event[]> events = new List<Event[]>();

	foreach(var e in EAC){
			events.Add(new Event[]
			{
				e, 
				new Event(string.Concat(e.Alias, "pC"), Controllability.Uncontrollable),
				new Event(string.Concat(e.Alias, "mC"), Controllability.Uncontrollable),
				new Event(string.Concat(e.Alias, "pN"), Controllability.Uncontrollable),
				new Event(string.Concat(e.Alias, "mN"), Controllability.Uncontrollable)			
			});
			
		}
	foreach(var e in EAuC){
		events.Add(new Event[]
		{
			e,
			new Event(string.Concat(e.Alias, "pC"), Controllability.Uncontrollable),
			new Event(string.Concat(e.Alias, "mC"), Controllability.Uncontrollable),
			new Event(string.Concat(e.Alias, "pN"), Controllability.Uncontrollable),
			new Event(string.Concat(e.Alias, "mN"), Controllability.Uncontrollable)
		});

	}

	List<Transition> trans = new List<Transition>();
	trans.AddRange(E.Transitions.ToList());
	foreach (var t in E.Transitions)
	{
		if (t.Origin != t.Destination)
		{
			if (EAC.Contains(t.Trigger))
			{
				var index = events.FindIndex(a => a[0] == t.Trigger);
				var tnew = new Transition(t.Origin, events.ElementAt(index)[(int)EventType.pN], t.Destination);
				trans.Add(tnew);
			}
			else if (EAuC.Contains(t.Trigger))
			{
				var s = new State(string.Concat(t.Origin.ToString(), t.Trigger.ToString(), t.Destination.ToString()));
				var index = events.FindIndex(a => a[0] == t.Trigger);
				var tnew = new Transition(t.Origin, events.ElementAt(index)[(int)EventType.mC], s);
				trans.Add(tnew);
				tnew = new Transition(s, events.ElementAt(index)[(int)EventType.pC], t.Destination);
				trans.Add(tnew);
				
				foreach(var te in E.Transitions){
					// verifies if there is a transition with uncontrollable event not under attack from the state q'
					if(te.Origin == t.Destination && !te.Trigger.IsControllable && E.Events.Except(EAuC).Contains(te.Trigger))
					{
						var se = new State(string.Concat(te.Origin.ToString(), te.Trigger.ToString(), te.Destination.ToString()));
						tnew = new Transition(s, te.Trigger, se);
						trans.Add(tnew);
						tnew = new Transition(se, events.ElementAt(index)[(int)EventType.pC], t.Destination);
						trans.Add(tnew);
					}
				}
				
			}
		}
	}

	trans.AddRange(E.Transitions.ToList());


	foreach (var t in trans)
	{
		Console.WriteLine(t + " ");

	}

	var T = toTransitionList(trans);
	ThetaE = new DeterministicFiniteAutomaton(T, E.InitialState, "TN");
	
	ThetaE.ShowAutomaton("TE");

}

static void NetworkEstimator(out DeterministicFiniteAutomaton ThetaN, DeterministicFiniteAutomaton G)
{
	//var events = new Ev //row: type of event; column: event
	List<Event[]> events = new List<Event[]>();

	foreach (Event e in G.Events)
	{
		events.Add(new Event[]
		{
				e,
				new Event(string.Concat(e.Alias, "pC"), Controllability.Uncontrollable),
				new Event(string.Concat(e.Alias, "mC"), Controllability.Uncontrollable),
				new Event(string.Concat(e.Alias, "pN"), Controllability.Uncontrollable),
				new Event(string.Concat(e.Alias, "mN"), Controllability.Uncontrollable)
		});

	}

	List<Transition> trans = new List<Transition>();
	
	foreach(var t in G.Transitions)
	{
		if(t.Trigger.IsControllable)
		{
			var index = events.FindIndex(a => a[0] == t.Trigger);
			var tnew = new Transition(t.Origin, events.ElementAt(index)[(int)EventType.pN], t.Destination);
			trans.Add(tnew);
		}
		else
		{
			var index = events.FindIndex(a => a[0] == t.Trigger);
			var tnew = new Transition(t.Origin, events.ElementAt(index)[(int)EventType.mC], t.Destination);
			trans.Add(tnew);
		}
	}

	trans.AddRange(G.Transitions.ToList());


	foreach (var t in trans)
	{
		Console.WriteLine(t + " ");

	}

	var T = toTransitionList(trans);
	ThetaN = new DeterministicFiniteAutomaton(T, G.InitialState, "TN");

	//ThetaN.ShowAutomaton("TN");
}

//Creates the Controller Estimator. This function receives a reference to new automaton and the original 
	//automaton of the plant under attack G. 
	static void ControllerEstimator(out DeterministicFiniteAutomaton ThetaC, DeterministicFiniteAutomaton G)
	{

		//var events = new Ev //row: type of event; column: event
		List<Event[]> events = new List<Event[]>();


		foreach (Event e in G.Events)
		{
			events.Add(new Event[]
			{
				e,
				new Event(string.Concat(e.Alias, "pC"), Controllability.Uncontrollable),
				new Event(string.Concat(e.Alias, "mC"), Controllability.Uncontrollable),
				new Event(string.Concat(e.Alias, "pN"), Controllability.Uncontrollable),
				new Event(string.Concat(e.Alias, "mN"), Controllability.Uncontrollable)
			});

		}

		List<Transition> trans = new List<Transition>();


		foreach (var t in G.Transitions)
		{
			if (t.Trigger.Controllability == Controllability.Controllable)
			{
				var index = events.FindIndex(a => a[0] == t.Trigger);
				var tnew = new Transition(t.Origin, events.ElementAt(index)[(int)EventType.mN], t.Destination);
				trans.Add(tnew);
			}
			else
			{
				var index = events.FindIndex(a => a[0] == t.Trigger);
				var tnew = new Transition(t.Origin, events.ElementAt(index)[(int)EventType.pC], t.Destination);
				trans.Add(tnew);
			}

		}
		
		foreach(var q in G.States)
		{
			foreach(var e in G.Events)
			{
				if(!e.IsControllable)
				{
					if(!isFeasible(G, e, q))
					{
						var index = events.FindIndex(a => a[0] == e);
						var tnew = new Transition(q, events.ElementAt(index)[(int)EventType.pC], q);
						trans.Add(tnew);					
					}					
				}
			}
		}

		
		trans.AddRange(G.Transitions.ToList());

		foreach (var l in events)
			{
				foreach (var ev in l)
				{
					Console.Write(ev + " ");
				}
				Console.WriteLine();
			}

		foreach (var t in trans)
		{
			Console.WriteLine(t + " ");

		}

	var T = toTransitionList(trans);
	ThetaC = new DeterministicFiniteAutomaton(T, G.InitialState, "TG");

	//ThetaC.ShowAutomaton("TG");


}



static bool isFeasible(DeterministicFiniteAutomaton G, AbstractEvent e, AbstractState q)
{
	foreach(var t in G.Transitions)
	{
		if(t.Origin == q && t.Trigger == e)
		{
			return true;
		}
	}
	return false;
	
}

static List<(AbstractState, AbstractEvent, AbstractState)> toTransitionList(List<Transition> tr)
{
	List<(AbstractState, AbstractEvent, AbstractState)> T = new List<(AbstractState, AbstractEvent, AbstractState)>();


	foreach (var t in tr)
	{
		T.Add(new Transition((AbstractState)t.Origin, (AbstractEvent)t.Trigger, (AbstractState)(t.Destination)));
	}
	
	return T;
}