public OptimizationStatistics GetOptimizationStatistics()
{
    long count = 0;
    var pairs = new HashSet<CharacteristicPair>();
    var predicatesByValues = new Dictionary<string, List<PredicateInfo>>();
    var intersects = new List<IntersectStatements>();
    var subjects = new HashSet<string>();
    var allProps = new HashSet<QName>();
    var containerCS = new Dictionary<string, Dictionary<string, CharacteristicSet>>(); //ключ - название контейнера, значение - словарь characteristicSets
    var predicatesById = new Dictionary<string, string>();
    var allSets = new HashSet<CharacteristicSet>();
    using (var ctx = new TransactionScope())
    {
        var axioms = ctx.Context.Axioms;
        var apps = axioms.GetSubjects(Logics.Names.Common.A, Names.ObjectApp.AppClass).Except(appsToExclude).ToList();
        foreach (var app in apps)
        {
            var appAlias = axioms.GetFact(app, Names.Container.Alias).GetValueOrDefault<string>();
            var props = axioms.GetFacts(app, Names.ObjectApp.Property).ToList();
            var elApp = axioms.GetSubjects(Logics.Names.Common.A, app).ToList();
            var currentSet = new HashSet<string>();
            var charasteristicSets = new Dictionary<string, CharacteristicSet>();//ключ - строка из элиасов атрибутов (предикатов-пропертей), разделенная запятыми
            // значение - количество субъектов с таким хар. сетом
            var countS = 0;
            foreach (var el in elApp)
            {
                var cs = new CharacteristicSet(appAlias);
                foreach (var prop in props)
                {
                    if (axioms.GetFacts(el, prop).Any()) //facts для multivalue
                    {
                        var pClientString = prop.ToClientString();
                        if (!predicatesById.ContainsKey(pClientString))
                        {
                            var pa = axioms.GetFact(prop, Names.ObjectApp.PropertyAlias).GetValueOrDefault<string>();
                            predicatesById[pClientString] = pa;
                        }

                        var pAlias = predicatesById[pClientString];
                        cs.AddPredicate(pAlias);
                    }
                }

                var csString = cs.GetKey();
                if (!charasteristicSets.ContainsKey(csString))
                {
                    charasteristicSets.Add(csString, cs);
                }
                charasteristicSets[csString].AddObject(el.ToClientString());
            }

            foreach (var cs in charasteristicSets)
            {
                allSets.Add(cs.Value);
            }

            containerCS.Add("c." + appAlias, charasteristicSets);
            foreach (var prop in props)
            {
                allProps.Add(prop);
                var pAlias = axioms.GetFact(prop, Platform.Names.ObjectApp.PropertyAlias).GetValueOrDefault<string>();
                var isCalculated = axioms.HasFact(prop, Data.Entity.Names.Common.PropertyAttributes, Platform.Names.Property.PropertyAttributeCalculated);
                var isMultivalue = axioms.HasFact(prop, Data.Entity.Names.Common.PropertyAttributes, Platform.Names.Property.PropertyAttributeMultiValue);
                var isReference = axioms.HasFact(prop, Platform.Names.Property.PropertyType, Platform.Names.Property.PropertyTypeInstance) || axioms.HasFact(prop, Platform.Names.Property.PropertyType, Platform.Names.ObjectApp.AppClass);
                string pName = "p." + appAlias + "." + pAlias;
                currentSet.Add(pName);
                var statements = axioms.GetStatementsForPredicate(prop);
                countS += statements.Count();
                var d = new Dictionary<string, long>();
                foreach (var st in statements)
                {
                    var s = st.Subject;
                    subjects.Add(s.ToString());
                    count++;
                    var objectStr = st.Object.ToString();
                    if (!d.ContainsKey(objectStr))
                    {
                        d.Add(objectStr, 0);

                    }
                    d[objectStr]++;
                }

                var pis = new List<PredicateInfo>();
                foreach (var kv in d)
                {
                        pis.Add(new PredicateInfo
                        {
                            Value = kv.Key,
                            Count = kv.Value,
                            IsCalculated = isCalculated ? 1 : 0,
                            IsMultivalueObject = isMultivalue ? 1 : 0,
                            IsReference = isReference ? 1 : 0
                        });
                }

                predicatesByValues[pName] = pis;
            }
            var currentSetList = currentSet.ToList();
        }

        var propsList = allProps.ToList();
        for (var i = 0; i < propsList.Count; i++)
        {
            for (var j = i + 1; j < propsList.Count; j++)
            {
                var p1 = propsList[i];
                var p2 = propsList[j];

                var p1App = axioms.GetSubjects(Platform.Names.ObjectApp.Property, p1).FirstOrDefault();
                var p2App = axioms.GetSubjects(Platform.Names.ObjectApp.Property, p2).FirstOrDefault();

                var p1AppAlias = axioms.GetFact(p1App, Platform.Names.Container.Alias).GetValueOrDefault<string>();
                var p2AppAlias = axioms.GetFact(p2App, Platform.Names.Container.Alias).GetValueOrDefault<string>();

                var p1InstanceApp = axioms.GetFact(p1, Platform.Names.ObjectApp.InstanceApp);
                var p2InstanceApp = axioms.GetFact(p2, Platform.Names.ObjectApp.InstanceApp);

                var p1Statements = axioms.GetStatementsForPredicate(p1);
                var p2Statements = axioms.GetStatementsForPredicate(p2);

                var p1Alias = "p." + p1AppAlias + "."+ axioms.GetFact(p1, Platform.Names.ObjectApp.PropertyAlias).GetValueOrDefault<string>();
                var p2Alias = "p." + p2AppAlias + "." + axioms.GetFact(p2, Platform.Names.ObjectApp.PropertyAlias).GetValueOrDefault<string>();

                if (p1App != null && p2App != null && p1App.Equals(p2App))
                {
                    var rrCount = p1Statements.Select(s => s.Subject).Intersect(p2Statements.Select(s => s.Subject)).Count();
                    intersects.Add(new IntersectStatements()
                    {
                        Type = "ss",
                        IntersectedStatements = rrCount,
                        Predicate1 = p1Alias,
                        Predicate2 = p2Alias
                    });
                }

                if (p1InstanceApp != null && p2InstanceApp != null && p1InstanceApp.Equals(p2InstanceApp))
                {
                    var ooCount = p1Statements.Select(s => s.Object).Intersect(p2Statements.Select(s => s.Object)).Count();
                    intersects.Add(new IntersectStatements
                    {
                        Type = "oo",
                        IntersectedStatements = ooCount,
                        Predicate1 = p1Alias,
                        Predicate2 = p2Alias
                    });
                }

                if (p1App != null && p2InstanceApp != null && p1App.Equals(p2InstanceApp))
                {
                    var soCount = p1Statements.Select(s => s.Subject).Intersect(p2Statements.Select(s => s.Object)).Count();
                    intersects.Add(new IntersectStatements
                    {
                        Type = "so",
                        IntersectedStatements = soCount,
                        Predicate1 = p1Alias,
                        Predicate2 = p2Alias
                    });
                }

                if (p2App != null && p1InstanceApp != null && p2App.Equals(p1InstanceApp))
                {
                    var osCount = p1Statements.Select(s => s.Object).Intersect(p2Statements.Select(s => s.Subject)).Count();
                    intersects.Add(new IntersectStatements
                    {
                        Type = "os",
                        IntersectedStatements = osCount,
                        Predicate1 = p1Alias,
                        Predicate2 = p2Alias,
                        App1 = p1AppAlias,
                        App2 = p2AppAlias,
                        PredicateId1 = p1.ToClientString(),
                    });
                }
            }
        }

        foreach (var i in intersects)
        {
            if (i.Type != "os" || i.IntersectedStatements == 0)
            {
                continue;
            }

            var p1Alias = i.Predicate1.Split('.').Last();
            var p2Alias = i.Predicate2.Split('.').Last();
            var css = allSets.Where(x => x.App == i.App1 && x.PredicatesSet.Contains(p1Alias)).ToList();
            var cso = allSets.Where(x => x.App == i.App2 && x.PredicatesSet.Contains(p2Alias)).ToList();

            foreach (var ss in css)
            {
                var ssObjects = ss.Subjects;
                foreach (var so in cso)
                {
                    long hsCount = 0;
                    var soObjects = so.Subjects;
                    var p1 = i.PredicateId1.ToQName();
                    var cp = new CharacteristicPair(so, ss);
                    if (!pairs.Contains(cp)) // linked by one predicate, if already processed - skip
                    {
                        foreach (var s in ssObjects)
                        {
                            var qObject = s.ToQName();
                            var vals = axioms.GetFacts(qObject, p1);
                            foreach (var val in vals)
                            {
                                if (soObjects.Contains(val.ToClientString()))
                                {
                                    hsCount++;
                                }
                            }
                        }

                        if (hsCount > 0)
                        {
                            cp.Count = hsCount;
                            pairs.Add(cp);
                        }
                    }
                }
            }
        }
    }

    var resultCsDict = new Dictionary<string, Dictionary<string, long>>();
    foreach (var cs in containerCS)
    {
        var ds = new Dictionary<string, long>();
        foreach (var csv in cs.Value)
        {
            ds[csv.Key] = csv.Value.Count;
        }
        resultCsDict.Add(cs.Key, ds);
    }

    var os = new OptimizationStatistics
    {
        StatementsCount = count,
        PredicatesByValues = predicatesByValues,
        SubjectsCount = subjects.Count,
        Intersects = intersects,
        CharacteristicSets = resultCsDict,
        Pairs = pairs
    };
    return os;
}
