// Basic User Signature
abstract sig User {
    id: one String,
    name: one String,
    surname: one String,
    email: one String,
    phoneNumber: one String
}

// Differentiating between Educator and Student
sig Educator extends User {
    department: one String,
    createdTournaments: set Tournament,
    createdBattles: set Battle,
    createdBadges: set Badge
}

sig Student extends User {
    grade: one Int,
    memberOf: set Group
}

// Group of Students
sig Group {
    id: one String,
    size: one Int,
    members: some Student,
    score: one Int,
    joinedTournaments: set Tournament
}

// Badge and Requisite
sig Badge {
    id: one String,
    name: one String,
    description: one String,
    requisites: set Requisite,
    obtainedBy: set Student
}

sig Requisite {
    id: one String,
    description: one String,
    achievedBy: set Student
}

// Tournament and Battle
sig Tournament {
    id: one String,
    startDate: one Date,
    endDate: one Date,
    participatingGroups: set Group,
    battles: set Battle
}

sig Battle {
    id: one String,
    startDate: one Date,
    endDate: one Date,
    participatingGroups: set Group
}

// Submission for Battles
sig Submission {
    id: one String,
    githubLink: one String,
    group: one Group,
    battle: one Battle,
    date: one Date
}

// Date Signature for scheduling
sig Date {
    year: Int,
    month: Int,
    day: Int
}

// Define a set to keep track of scored groups for each educator and battle
sig EducatorBattleScore {
  educator: Educator,
  battle: Battle,
  score: Int,
  group: Group
}

// Define a relation to represent grade modifications by educators
sig GradeModification {
  educator: Educator,
  student: Student,
  newGrade: Int
}

// Define month sets as constants
one sig ThirtyOneDayMonths {
    months: set Int
} {
    months = 1 + 3 + 5 + 7 + 8 + 10 + 12
}

one sig ThirtyDayMonths {
    months: set Int
} {
    months = 4 + 6 + 9 + 11
}

one sig February {
    months: set Int
} {
    months = 2
}
// Constraints
fact {
    // Each group has members and their number should match the group's size
    all g: Group | #g.members = g.size

    // A battle belongs to only one tournament
    all b: Battle | one t: Tournament | b in t.battles

    // Submission's group must be part of the battle's participating groups
    all s: Submission | s.group in s.battle.participatingGroups

    // Badges are awarded to students who have met all requisites
    all b: Badge, s: Student | s in b.obtainedBy iff all r: b.requisites | s in r.achievedBy
}


// Use the constants in the fact
fact {
    all d: Date {
        d.year > 0
        d.month > 0 and d.month <= 12
        d.day > 0
        // Check for the number of days in each month
        d.month in ThirtyOneDayMonths.months => d.day <= 31
        d.month in ThirtyDayMonths.months => d.day <= 30
        d.month in February.months => d.day <= 28
    }
}

// A student cannot be part of two different groups at the same time
fact noOverlappingGroupMembership {
  all s: Student | lone g: Group | s in g.members
}

// An educator cannot create two tournaments with the same name
fact uniqueTournamentNames {
  all t1, t2: Tournament | t1 != t2 => t1.name != t2.name
}

// Define a predicate to check for overlapping battles
pred overlappingBattles[b1, b2: Battle] {
  b1 != b2 and
  (b1.startDate.year < b2.endDate.year or
   (b1.startDate.year = b2.endDate.year and
    (b1.startDate.month < b2.endDate.month or
     (b1.startDate.month = b2.endDate.month and
      b1.startDate.day < b2.endDate.day)))) and
  (b2.startDate.year < b1.endDate.year or
   (b2.startDate.year = b1.endDate.year and
    (b2.startDate.month < b1.endDate.month or
     (b2.startDate.month = b1.endDate.month and
      b2.startDate.day < b1.endDate.day))))
}

// A group cannot join two battles in the same tournament at the same time
fact noOverlappingBattlesInTournament {
  all g: Group, t: Tournament | 
    let battlesInTournament = t.battles & g.joinedTournaments.battles |
    no disj b1, b2: battlesInTournament |
      overlappingBattles[b1, b2]
}


// A group cannot submit more than one solution for a battle
fact uniqueSubmissionPerGroupPerBattle {
  all b: Battle, g: Group | lone s: Submission | s.battle = b and s.group = g
}

// A badge can only be obtained by a student if all requisites are met
fact badgeRequisitesMet {
  all b: Badge | all s: Student | 
    s in b.obtainedBy iff (all r: b.requisites | s in r.achievedBy)
}

// A tournament cannot have battles that overlap in time
fact noOverlappingBattles {
  all disj t: Tournament, b1, b2: t.battles | 
    !(overlappingBattles[b1, b2])
}

// A student can only be awarded a badge once
fact uniqueBadgePerStudent {
  all s: Student | all disj b1, b2: Badge | 
    not (s in b1.obtainedBy and s in b2.obtainedBy and b1 = b2)
}

// Educators cannot score the same group twice for the same battle
fact uniqueScoringPerGroupPerBattle {
  all e: Educator, b: Battle, g: Group |
    lone eb: EducatorBattleScore | eb.educator = e and eb.battle = b and eb.group = g
}

// Educators can modify student grades
fact educatorsCanModifyGrades {
  all em: GradeModification |
    let e = em.educator,
        s = em.student,
        newGrade = em.newGrade |
    e in Educator and s in Student and newGrade > 0
}

// A student\’s grade can only be modified by an educator
fact gradeModificationByEducator {
  all s: Student | all g: s.grade | some gm: GradeModification | gm.student = s and gm.newGrade=g
}
