## RTT Simulation Model - Version 2 
### Build 3.1.0
#### Created date: 06/09/2021
#### Updated date: 28/02/2022
#### Notes:
###### Script requires pathway generation script to have been run first, 
###### to initialise trajectory objects used by this simmer.


#### 0. Clear console and environment for visibility ----
cat("\014")
objectsToRemove <- ls()
objectsToRemove <- objectsToRemove[!(objectsToRemove %in% c("masterTrajectoriesList","masterTrajectoriesList_v2","masterTrajectoriesList_v2a","masterTrajectoriesList_v2b","masterTrajectoriesList_v3a","masterTrajectoriesList_v3b","masterTrajectoriesList_v4a","masterTrajectoriesList_v4b"))]
rm(list = objectsToRemove)
processStartTime <- Sys.time()

#### 1. Load Libraries ----
library(infoPack)
library(dplyr)
library(tidyr)
library(DBI)
library(simmer)
library(simmer.plot)
library(DescTools)
library(lubridate)
library(ggplot2)

#### 2. Set Parameters ----
niterations <- 8 # model is fine tuned using 8 iterations, then once calibrated a full 50 iteration monte carlo loop is run
parameters <- list(
  specialty = "101" # 101: urology
  ,mode = "Random" # must be fixed (for mean clock start forecast) or random (for random clock start within forecast 80%ile range)
  ,simulationStart = as.Date("2021-09-01")
  ,simulationEnd = as.Date("2022-03-31")
)
boostActivityOnRTT_IP <- 0 # calibrate the proportion of inpatient activity estimated to affect ticking RTT clocks (+ve value increases percentage, -ve value decreases percentage)
boostActivityOnRTT_OP <- -0.6 # same as above

#### 3. Extract Datasets from SQL Warehouse ----
clockStartForecast <- runSQL(paste0("SELECT * FROM BI_REPORTING.Shiny.AP2_NewClockStartForecast WHERE GroupedSpecialtyCode = '",parameters$specialty,"'"))
activityForecast <- runSQL(paste0("EXEC BI_REPORTING.Shiny.AP2_ActivityForecast_H2 @SPECIALTY = '",parameters$specialty,"'"))
activityClockStatus <- runSQL("EXEC BI_REPORTING.Shiny.AP2_ActivityClockStatusPull")
currentPTL <- runSQL("EXEC BI_REPORTING.Shiny.AP2_PTLActivitiesPull")
rottDataset <- runSQL("EXEC BI_REPORTING.Shiny.AP2_PathwayDetails_PercentileExclude_ROTTDelayPull")

#### 4. Build Custom Functions ----
buildcal <- function(startdate,enddate){ # Create a calendar table based on two dates
  data.frame(datekey = seq.Date(from = as.Date(startdate), to = as.Date(enddate), by = "day")) %>%
    mutate(
      yearmonth = paste0(lubridate::year(datekey),sprintf("%02d",lubridate::month(datekey)))
      ,mrank = dense_rank(yearmonth)
      ,weekdayname = lubridate::wday(datekey,label = TRUE)
      ,dayval = case_when(weekdayname %in% c("Mon","Tue","Wed","Thu","Fri") ~ 1,TRUE ~ 0)
    ) %>%
    group_by(yearmonth) %>%
    mutate(
      monthstarting = min(datekey)
      ,groupsum = max(cumsum(dayval))
      
    ) %>%
    group_by(yearmonth,dayval) %>%
    mutate(dayinmonth = row_number()) %>%
    mutate(dayinmonth = case_when(dayval == 1 ~ dayinmonth, TRUE ~ as.integer(NA)))
}

build_referral_spread <- function(startdate,enddate,referralsdataframe,monthfield,referralsfield){ # create a daily calendar distribution of referrals, based on a monthly referral figure
  datafield <- enexpr(referralsfield)
  
  referrals <- buildcal(as.Date(startdate),as.Date(enddate)) %>%
    left_join(referralsdataframe,by = c("monthstarting" = monthfield)) %>%
    mutate(basereferralsperday = floor(!!datafield/groupsum), bonusreferralday = floor((dayinmonth * (((!!datafield%%groupsum))/groupsum)))) %>%
    mutate(bonusreferralday = case_when(dayinmonth == groupsum ~ !!datafield%%groupsum, TRUE ~ bonusreferralday)) %>% ## added to prevent weird flooring error taking 1 off remainder in certain circumstances
    filter(dayval == 1) %>%
    mutate(bonusreferrals = case_when(bonusreferralday == 0 ~ 0,bonusreferralday == lag(bonusreferralday,1) ~ 0,TRUE ~ 1)) %>%
    mutate(finalreferrals = basereferralsperday + bonusreferrals) %>%
    dplyr::select(datekey,finalreferrals) %>%
    ungroup()
  
  calendarreferrals <- buildcal(as.Date(startdate),as.Date(enddate)) %>%
    left_join(referrals) %>%
    ungroup() %>%
    mutate(timeindex = row_number())
  
  calendarreferrals$finalreferrals[is.na(calendarreferrals$finalreferrals)] <- 0
  
  calendarreferrals %>%
    dplyr::select(monthstarting,datekey,weekdayname,timeindex,finalreferrals)
}

rbetween <- function(a,b){
  runif(1,a,b)
}

runString <- function(x){ # Run string as R code
  eval(parse(text = x))
}

ifNA <- function(x,y){ # Substitute NA for value
  if(is.na(x)){
    y
  } else {
    x
  }
}

rollDice <- function(n){ # Roll a dice to decide on an outcome based on a numeric vector of samples
  if(!is.numeric(n)){stop("Error: Roll dice function needs a numeric vector")}
  
  probabilityRange <- data.frame(
    probabilityCap = n
  ) %>%
    mutate(
      runningSum = cumsum(probabilityCap)
      ,grandTotal = max(runningSum)
      ,probability = runningSum/grandTotal
      ,rank = row_number()
    )
  
  diceRoll <- runif(1,0,1)
  
  probabilityRange %>%
    filter(diceRoll <= probability) %>%
    dplyr::select(rank) %>%
    head(1) %>%
    as.integer()
}

rottCurveFx <- function(specialty,urgency,clocktype){ # Cumulative probability curve for clock stops due to ROTT (reasons other than treatment)
  
  rottData <- rottDataset %>%
    filter(Phase4AggregatedCode == specialty, PathwayUrgency == urgency, StartType == clocktype) %>%
    mutate(percentile85 = quantile(ROTTDelay,0.90)) %>%
    filter(ROTTDelay <= percentile85) 
  curve <- ecdf(rottData$ROTTDelay)
  rottCurve <- data.frame(
    days = 1:max(rottData$ROTTDelay) 
  ) %>%
    mutate(curve = curve(days))
  
  randomNumber <- runif(1,0,1)
  
  day <- rottCurve %>%
    filter(curve <= randomNumber) %>%
    dplyr::select(days) %>%
    tail(1)
  
  if_else(is.na(day[1,1]),as.integer(0),day[1,1])
}

buildcal1 <- function(extractdate){
  e <- as.Date(extractdate)
  
  data.frame(
    datekey = seq.Date(from = e, by = "day", length.out = 365)
    ,index = 1:365
  ) %>%
    mutate(monthstarting = as.Date(paste0(lubridate::year(datekey),'-',lubridate::month(datekey),'-01'))) %>%
    mutate(lastdayofmonth = ceiling_date(datekey,unit = "month")-1, lastdayflag = case_when(lastdayofmonth == datekey ~ 1,TRUE ~ 0))
  
  ## TBC: add a 'last day of month' flag
}

#### 5. Create Calendar ----
maxdays <- max(currentPTL$CurrentIndex) - 1
mastercal <- buildcal(parameters$simulationStart,parameters$simulationEnd)
mastercal <- mastercal %>%
  ungroup() %>%
  mutate(timeindex = row_number()) %>%
  mutate(timeindex = timeindex + maxdays)
parameters[["simulationFinalIndex"]] <- max(mastercal$timeindex)

#### 6. Load Trajectories ----
## Placeholder - cannot currently come up with a way to store the trajectory objects in a saveable R data structure without an error occuring 
## This is why generate pathways script must be run first

#### 7. Set Seed ----
set.seed(2021)


#### 8. Demand Generators ----
generateNewDemand <- function(urgency,clocktype,mode){ # Create function which generates an arrivals pattern
  if(mode == "Fixed"){
    tempclock <- clockStartForecast %>%
      filter(Urgency == urgency, PathwayType == clocktype)  
    referralCalendar <- build_referral_spread(
      parameters$simulationStart
      ,parameters$simulationEnd
      ,tempclock
      ,"ForecastMonth"
      ,Mean
    )
  } else if(mode == "Random"){
    tempclock <- clockStartForecast %>%
      filter(Urgency == urgency, PathwayType == clocktype) %>%
      mutate(startsThisMonth = NA)
    for(n in 1:nrow(tempclock)){
      tempclock$startsThisMonth[n] <- rbetween(tempclock$Lower80[n],tempclock$Upper80[n])
    }
    referralCalendar <- build_referral_spread(
      parameters$simulationStart
      ,parameters$simulationEnd
      ,tempclock
      ,"ForecastMonth"
      ,startsThisMonth
    )
  }
  referralCalendar$finalreferrals[referralCalendar$finalreferrals<0] <- 0
  referralCalendar$timeindex <- referralCalendar$timeindex + maxdays
  rep(referralCalendar$timeindex,referralCalendar$finalreferrals)
}


#### 8a. Identify demand cohorts from existing PTL ----
ptlData <- currentPTL %>%
  mutate(uniqueID = row_number()
         ,parentActivities = New_FollowUp_Flag
  ) %>%
  filter(Phase4AggregatedCode == parameters$specialty)

for(n in 1:as.integer(max(ptlData$ActivityIndex))){
  ptlReplace <- ptlData %>%
    filter(ActivityIndex == n) %>%
    left_join(
      {ptlData %>%
          filter(ActivityIndex == n - 1) %>%
          dplyr::select(PeriodID,ParentNF = parentActivities) }
      ,by = c("PeriodID")
    ) %>%
    mutate(
      parentActivities = paste0(if_else(is.na(ParentNF),'',paste0(ParentNF,'/')),New_FollowUp_Flag)
    ) %>%
    dplyr::select(uniqueID, newActivities = parentActivities)
  
  ptlData <- ptlData %>%
    left_join(ptlReplace,by = c("uniqueID")) %>%
    mutate(parentActivities = if_else(is.na(newActivities),parentActivities,newActivities)) %>%
    dplyr::select(-newActivities)
}

ptlManip <- ptlData %>%
  mutate(nextActivity = case_when(
    !is.na(FutureWL_DTA) ~ FutureWL_IntMan
    ,!is.na(FutureOP_ApptDate) ~ FutureOP_NFFlag
  )) %>%
  group_by(PeriodID) %>%
  arrange(desc(ActivityIndex)) %>%
  mutate(lastIndex = row_number()) %>%
  filter(lastIndex == 1) %>%
  ungroup() %>%
  dplyr::select(
    ReferralUrgency
    ,ClockType
    ,Phase4AggregatedCode
    ,parentActivities
    ,nextActivity
    ,StartDate
    ,StartFromIndex
  ) %>%
  group_by(
    ReferralUrgency
    ,ClockType
    ,parentActivities
  ) %>%
  summarise(volume = n()) %>%
  mutate(pairTrajectory = parentActivities,trajectoryExists = NA) 

ptlManip$pairTrajectory <- paste0("Start/",ptlManip$pairTrajectory)
ptlManip$pairTrajectory <- gsub("/NA","",ptlManip$pairTrajectory)
ptlManip$pairTrajectory <- gsub("/DC","/IP:DC",ptlManip$pairTrajectory)
ptlManip$pairTrajectory <- gsub("/EL IP","/IP:EL IP",ptlManip$pairTrajectory)
ptlManip$pairTrajectory <- gsub("/N","/OP:N",ptlManip$pairTrajectory)
ptlManip$pairTrajectory <- gsub("/F","/OP:F",ptlManip$pairTrajectory)

##### Confirm which trajectories exist
for(n in 1:nrow(ptlManip)){
  ptlManipCurrent <- ptlManip[n,]
  trajectoryLengthCheck <- runString(
    paste0(
       "length("
      ,"masterTrajectoriesList_v4b$`"
      ,parameters$specialty
      ,"_"
      ,ptlManipCurrent$ReferralUrgency
      ,"_"
      ,ptlManipCurrent$ClockType
      ,"`$`"
      ,ptlManipCurrent$pairTrajectory
      ,"`"
      ,")"
    )
  )
  if(trajectoryLengthCheck > 0){
    ptlManip$trajectoryExists[n] <- 1
  } else {
    ptlManip$trajectoryExists[n] <- 0
  }
}

#### 8b. Create reserve trajectories to be used if current waiters do not match historic pathways ----
reserveTrajectories <- list(
  'Cancer' = trajectory() %>%
    set_attribute("Backup Trajectory Used",1) %>%
    seize("Follow Up_Cancer") %>%
    timeout(1) %>%
    release("Follow Up_Cancer") %>%
    seize("ClockStop") %>%
    set_attribute('ClockStop_Treat',1) %>%
    timeout(0) %>%
    release("ClockStop")
  ,'Urgent' = trajectory() %>%
    set_attribute("Backup Trajectory Used",1) %>%
    seize("Follow Up_Urgent") %>%
    timeout(1) %>%
    release("Follow Up_Urgent") %>%
    seize("ClockStop") %>%
    set_attribute('ClockStop_Treat',1) %>%
    timeout(0) %>%
    release("ClockStop")
  ,'Routine' = trajectory() %>%
    set_attribute("Backup Trajectory Used",1) %>%
    seize("Follow Up_Routine") %>%
    timeout(1) %>%
    release("Follow Up_Routine") %>%
    seize("ClockStop") %>%
    set_attribute('ClockStop_Treat',1) %>%
    timeout(0) %>%
    release("ClockStop")
)


#### 9. Identify Unique Cohorts ----
uniqueCohorts <- clockStartForecast %>%
  dplyr::select(Urgency,PathwayType) %>%
  unique()

#### 10. Capacity timetables ----
activityOnRTTProportions <- activityClockStatus %>%
  filter(Phase4AggregatedCode == parameters$specialty) %>%
  group_by(Pod1,Urgency) %>%
  summarise(
    TotalActivity = sum(Activity,na.rm=TRUE)
    ,OnTickingClock = sum(ActivityOnTickingClock)
  ) %>%
  ungroup() %>%
  group_by(Pod1) %>%
  mutate(PodSum = max(cumsum(TotalActivity)),AvailableToRTT = OnTickingClock/PodSum)


activityOnRTTProportions <- data.frame(
  Pod1 = c(rep("DC",3),rep("EL IP",3),rep("OP:N",3),rep("OP:F",3))
  ,Urgency = rep(c("Cancer","Routine","Urgent"),4)
) %>%
  left_join(activityOnRTTProportions, by = c("Pod1","Urgency"))  %>%
  mutate(
    OnTickingClock = if_else(is.na(OnTickingClock),0,OnTickingClock)
    ,TotalActivity = if_else(is.na(TotalActivity),0,TotalActivity)
    ,PodSum = if_else(is.na(PodSum),0,PodSum)
    
  ) %>%
  group_by(Pod1) %>%
  mutate(PodSum = max(cumsum(TotalActivity))) %>%
  ungroup() %>%
  mutate(AvailableToRTT = if_else(is.na(AvailableToRTT),0,AvailableToRTT))


if(boostActivityOnRTT_OP != 0){
  activityOnRTTProportions <- activityOnRTTProportions %>%
    mutate(OnTickingClock = case_when(
      !(Pod1 %in% c("OP:N","OP:F")) ~ OnTickingClock
      ,(OnTickingClock * (1+boostActivityOnRTT_OP)) <= TotalActivity ~ OnTickingClock * (1+boostActivityOnRTT_OP)
      ,TRUE ~ TotalActivity
    )
    ) %>%
    mutate(AvailableToRTT = OnTickingClock/PodSum)
}
if(boostActivityOnRTT_IP != 0){
  activityOnRTTProportions <- activityOnRTTProportions %>%
    mutate(OnTickingClock = case_when(
      !(Pod1 %in% c("DC","EL IP")) ~ OnTickingClock
      ,(OnTickingClock * (1+boostActivityOnRTT_IP)) <= TotalActivity ~ OnTickingClock * (1+boostActivityOnRTT_IP)
      ,TRUE ~ TotalActivity
    )
    ) %>%
    mutate(AvailableToRTT = OnTickingClock/PodSum)
}

activityForecastByUrgency <- activityForecast %>%
  group_by(Pod1,ForecastMonth) %>%
  summarise(TotalExpectedActivity = sum(Activity,na.rm=TRUE)) %>%
  left_join(activityOnRTTProportions,by=c("Pod1")) %>%
  mutate(AvailableActivity = round(TotalExpectedActivity * AvailableToRTT,0)) %>%
  dplyr::select(Pod1,ForecastMonth,Urgency,AvailableActivity) %>%
  filter(ForecastMonth >= parameters$simulationStart, ForecastMonth <= parameters$simulationEnd) %>%
  mutate(ResourceName = case_when(
    Pod1 == 'OP:N' ~ 'New'
    ,Pod1 == 'OP:F' ~ 'Follow Up'
    ,Pod1 == 'DC' ~ 'Day Case'
    ,Pod1 == 'EL IP' ~ 'Elective'
  ))

uniqueActivityCohorts <- activityForecastByUrgency %>%
  dplyr::select(Pod1,Urgency,ResourceName) %>%
  unique()

capacityTimetable <- list()
for(n in 1:nrow(uniqueActivityCohorts)){
  calendar <- activityForecastByUrgency %>%
    filter(Urgency == uniqueActivityCohorts$Urgency[n],Pod1 == uniqueActivityCohorts$Pod1[n]) %>%
    build_referral_spread(
      parameters$simulationStart
      ,parameters$simulationEnd
      ,.
      ,"ForecastMonth"
      ,AvailableActivity
    ) 
  calendar$timeindex <- calendar$timeindex + maxdays
  itemName <- paste0(uniqueActivityCohorts$ResourceName[n],"_",uniqueActivityCohorts$Urgency[n])
  capacityTimetable[[itemName]] <- schedule(
    calendar$timeindex
    ,calendar$finalreferrals
  )
}


#### 11. Simmer Function ----
runSimulation <- function(i){
  
  simulationStartTime <- Sys.time()
  
  sim <- simmer(log_level = 0)
  
  # Add demand generators for existing clocks ----
  
  for(n in 1:nrow(ptlManip)){
    ptlManipCurrent <- ptlManip[n,]
    
    startingIndices <- ptlData %>%
      mutate(nextActivity = case_when(
        !is.na(FutureWL_DTA) ~ FutureWL_IntMan
        ,!is.na(FutureOP_ApptDate) ~ FutureOP_NFFlag
      )) %>%
      group_by(PeriodID) %>%
      arrange(desc(ActivityIndex)) %>%
      mutate(lastIndex = row_number()) %>%
      filter(lastIndex == 1) %>%
      ungroup() %>%
      dplyr::select(
        ReferralUrgency
        ,ClockType
        ,Phase4AggregatedCode
        ,parentActivities
        ,nextActivity
        ,StartDate
        ,StartFromIndex
      ) %>%
      filter(
        ReferralUrgency == ptlManipCurrent$ReferralUrgency
        ,ClockType == ptlManipCurrent$ClockType
        ,parentActivities == ptlManipCurrent$parentActivities
      ) %>%
      dplyr::select(StartFromIndex) 
    startingIndices <- sort(startingIndices$StartFromIndex)
    
    sim %>%
      add_generator(
        name_prefix = paste0("backlog_",ptlManipCurrent$ReferralUrgency,"_",ptlManipCurrent$ClockType,"_iteration(",n,"):")
        ,if(ptlManipCurrent$trajectoryExists == 1){
          runString(paste0("masterTrajectoriesList_v4b$`",parameters$specialty,"_",ptlManipCurrent$ReferralUrgency,"_",ptlManipCurrent$ClockType,"`$`",ptlManipCurrent$pairTrajectory,"`"))
        } else if(ptlManipCurrent$ReferralUrgency == "Cancer"){
          reserveTrajectories$Cancer
        } else if(ptlManipCurrent$ReferralUrgency == "Urgent"){
          reserveTrajectories$Urgent
        } else if(ptlManipCurrent$ReferralUrgency == "Routine"){
          reserveTrajectories$Routine
        }
        ,at(startingIndices)
        ,mon=2
      )
  }
  
  # Add demand generators for new clocks ----
  for(n in 1:nrow(uniqueCohorts)){
    sim %>%
      add_generator(
        name_prefix = paste0("new_",uniqueCohorts$Urgency[n],"_",uniqueCohorts$PathwayType[n],":")
        ,runString(paste0("masterTrajectoriesList_v4a$`",parameters$specialty,"_",uniqueCohorts$Urgency[n],"_",uniqueCohorts$PathwayType[n],"`$Start"))
        ,at(generateNewDemand(uniqueCohorts$Urgency[n],uniqueCohorts$PathwayType[n],parameters$mode))
        ,mon=2
      )
  }
  
  # Add resources ----
  for(resource in names(capacityTimetable)){
    sim %>%
      add_resource(resource,capacity = capacityTimetable[[resource]])
  }
  
  # Resource allocation monitors ----
  buildMonitor <- function(activity){
    trajectory() %>%
      set_global(paste0("attended_",activity,"_Cancer_today"),0) %>%
      set_global(paste0("attended_",activity,"_Urgent_today"),0) %>%
      set_global("rollback",1) %>%
      ## Rollback point begins here
      ## See if any cancer capacity can roll over into urgent
      timeout(0.1) %>%
      set_attribute(paste0(activity,"_Cancer_reallocation_checked_at"),values = function(){simmer::now(sim)}) %>%
      branch(function(){
        seentoday <- get_global(sim,paste0("attended_",activity,"_Cancer_today"))
        dailycapacity <- get_capacity(sim,paste0(activity,"_Cancer"))
        if(seentoday < dailycapacity){
          1
        } else {
          0
        }
      }
      ,continue = c(TRUE)
      ,trajectory() %>%
        set_capacity(
          resource = paste0(activity,"_Urgent")
          ,value = function(){
            seentoday <- get_global(sim,paste0("attended_",activity,"_Cancer_today"))
            dailycapacity <- get_capacity(sim,paste0(activity,"_Cancer"))
            dailycapacity - seentoday
          }
          ,mod = "+"
        ) %>%
        set_attribute(paste0("reallocated_",activity,"_Cancer_to_Urgent"),function(){
          seentoday <- get_global(sim,paste0("attended_",activity,"_Cancer_today"))
          dailycapacity <- get_capacity(sim,paste0(activity,"_Cancer"))
          dailycapacity - seentoday
        })
      ) %>%
      ## See if any urgent capacity can rollover into routine
      timeout(0.1) %>%
      set_attribute(paste0(activity,"_Urgent_reallocation_checked_at"),values = function(){simmer::now(sim)}) %>%
      branch(function(){
        seentoday <- get_global(sim,paste0("attended_",activity,"_Urgent_today"))
        dailycapacity <- get_capacity(sim,paste0(activity,"_Urgent"))
        if(seentoday < dailycapacity){
          1
        } else {
          0
        }
      }
      ,continue = c(TRUE)
      ,trajectory() %>%
        set_capacity(
          resource = paste0(activity,"_Routine")
          ,value = function(){
            seentoday <- get_global(sim,paste0("attended_",activity,"_Urgent_today"))
            dailycapacity <- get_capacity(sim,paste0(activity,"_Urgent"))
            dailycapacity - seentoday
          }
          ,mod = "+"
        ) %>%
        set_attribute("reallocated_Urgent_to_Routine_cap",function(){
          seentoday <- get_global(sim,paste0("attended_",activity,"_Urgent_today"))
          dailycapacity <- get_capacity(sim,paste0(activity,"_Urgent"))
          dailycapacity - seentoday
        })
      ) %>%
      ## Progress to end of day
      set_global(paste0("attended_",activity,"_Cancer_today"),0) %>%
      set_global(paste0("attended_",activity,"_Urgent_today"),0) %>%
      timeout(0.8) %>%
      simmer::rollback(9)
  }
  
  for(activity in c("New","Follow Up","Day Case","Elective")){
    sim %>%
      add_generator(paste0(activity,"_capacity_monitor"),buildMonitor(activity),at(1),mon = 2) 
  }
  
  # Enable clock stops only from simulation start onwards ----
  sim %>%
    add_resource("ClockStop",capacity = schedule(c(0,maxdays + 1),c(0,Inf))) # This prevents any pathways from having a clock stop before the simulation period begins, so that the starting PTL matches correctly
  
  # Enable ROTT timers only from fixed point onwards ----
  sim %>%
    add_resource("ReleaseROTTs",capacity = schedule(c(0,maxdays + 1),c(0,Inf))) # This prevents any pathways from having a clock stop before the simulation period begins, so that the starting PTL matches correctly
  
  # Run simulation ----
  sim %>%
    run(until = parameters$simulationFinalIndex+1)
  
  # Collate simulation output ----
  
  ## Raw outputs ----
  resources <- sim %>%
    get_mon_resources()
  
  arrivals <- sim %>%
    get_mon_arrivals(ongoing = TRUE) %>%
    unique()
  
  arrivals$end_time <- floor(arrivals$end_time)
  arrivals$end_time[is.na(arrivals$end_time)] <- Inf
  
  attributes <- sim %>%
    get_mon_attributes()
  attributes$time <- floor(attributes$time)
  
  ## Clock starts ----
  clockStartsInmodel <- arrivals %>%
    filter(name %like% 'new_%') %>%
    left_join(mastercal,by = c("start_time" = "timeindex")) %>%
    mutate(
      Urgency = case_when(
        name %like% '%Cancer%' ~ 'Cancer'
        ,name %like% '%Urgent%' ~ 'Urgent'
        ,name %like% '%Routine%' ~ 'Routine'
      )
      ,ClockType = case_when(
        name %like% '%New Pathway%' ~ 'New Pathway'
        ,name %like% '%Existing Pathway%' ~ 'Existing Pathway'
      )
    ) %>%
    group_by(
      monthstarting, yearmonth, Urgency, ClockType
    ) %>%
    summarise(
      ClockStarts = n()
    ) %>%
    left_join(
      clockStartForecast
      ,by = c("ClockType" = "PathwayType","Urgency" = "Urgency","monthstarting" = "ForecastMonth")
    )
  
  ## Activity data ----
  activityCheck <- attributes %>%
    mutate(time = floor(time)) %>%
    filter(key %like% 'Attended%') %>%
    mutate(
      Pod = gsub('Attended_','',key)
      ,Urgency = case_when(
        name %like% '%Cancer%' ~ 'Cancer'
        ,name %like% '%Urgent%' ~ 'Urgent'
        ,name %like% '%Routine%' ~ 'Routine'
      )
    ) %>%
    left_join(mastercal,by = c("time"="timeindex")) %>%
    group_by(Pod,monthstarting) %>%  
    summarise(Activity = n()) %>%
    left_join(
      {
        activityForecastByUrgency %>%
          mutate(Pod = case_when(
            Pod1 == 'DC' ~ 'IP:DC'
            ,Pod1 == 'EL IP' ~ 'IP:EL IP'
            ,TRUE ~ Pod1
          )) %>%
          group_by(Pod, ForecastMonth) %>%
          summarise(AvailableActivity = sum(AvailableActivity))
      }
      ,by = c(
        "Pod" = "Pod"
        ,"monthstarting" = "ForecastMonth"
      )
    ) %>%
    mutate(
      allCapacityUsed = case_when(
        Activity == AvailableActivity ~ TRUE
        ,TRUE ~ FALSE
      )
      ,proportionCapacityUsed = scales::percent(
        Activity/AvailableActivity
      )
    )
  
  ## Derive waiting lists ----
  
  adm_indicator <- attributes %>%
    filter(key == "AdmittedInd") %>%
    group_by(name) %>%
    arrange(desc(time)) %>%
    mutate(rank = row_number()) %>%
    ungroup() %>%
    filter(rank == 1) %>%
    dplyr::select(name, value) %>%
    mutate(AdmittedInd = case_when(
      value == 1 ~ 'Admitted'
      ,TRUE ~ 'NonAdmitted'
    )) %>%
    dplyr::select(-value)
  
  offsetDays <- -1
  dailywl <- buildcal1(parameters$simulationStart + offsetDays) %>%
    mutate(index = index + maxdays + offsetDays) %>% 
    mutate(index_join = index + 0.9, dummy = TRUE) %>%
    left_join(arrivals %>% mutate(dummy = TRUE) %>% filter(start_time != -1)) %>%
    filter(start_time <= index_join, end_time >= index_join) %>%
    mutate(dummy = TRUE) %>%
    left_join(adm_indicator, by = c("name")) %>%
    mutate(Urgency = case_when(
      name %like% '%Cancer_New Pathway%' ~ 'Cancer - New Pathway'
      ,name %like% '%Cancer_Existing Pathway%' ~ 'Cancer - Existing Pathway'
      ,name %like% '%Urgent_New Pathway%' ~ 'Urgent - New Pathway'
      ,name %like% '%Urgent_Existing Pathway%' ~ 'Urgent - Existing Pathway'
      ,name %like% '%Routine_New Pathway%' ~ 'Routine - New Pathway'
      ,name %like% '%Routine_Existing Pathway%' ~ 'Routine - Existing Pathway'
    )) %>%
    filter(!(name %in% c("New_capacity_monitor0","Follow Up_capacity_monitor0","Day Case_capacity_monitor0","Elective_capacity_monitor0"))) %>%
    mutate(waitdays = index - start_time) %>%
    mutate(
      `0-18 Weeks` = case_when(waitdays <= 18*7 ~ 1, TRUE ~ 0)
      ,`18-40 Weeks` = case_when(waitdays <= 40*7 & waitdays > 18*7 ~ 1, TRUE ~ 0)
      ,`40-52 Weeks` = case_when(waitdays <= 52*7 & waitdays > 40*7 ~ 1, TRUE ~ 0)
      ,`52-70 Weeks` = case_when(waitdays <= 70*7 & waitdays > 52*7 ~ 1, TRUE ~ 0)
      ,`70-104 Weeks` = case_when(waitdays <= 104*7 & waitdays > 70*7 ~ 1, TRUE ~ 0)
      ,`104+ Weeks` = case_when(waitdays > 104*7 ~ 1, TRUE ~ 0)
      ,TotalWaits = 1
    ) %>%
    group_by(datekey,lastdayofmonth,Urgency,AdmittedInd) %>%
    summarise(
      `0-18 Weeks` = sum(`0-18 Weeks`,na.rm = TRUE)
      ,`18-40 Weeks` = sum(`18-40 Weeks`,na.rm = TRUE)
      ,`40-52 Weeks` = sum(`40-52 Weeks`,na.rm = TRUE)
      ,`52-70 Weeks` = sum(`52-70 Weeks`,na.rm = TRUE)
      ,`70-104 Weeks` = sum(`70-104 Weeks`,na.rm = TRUE)
      ,`104+ Weeks` = sum(`104+ Weeks`,na.rm = TRUE)
      ,TotalPTL = sum(TotalWaits,na.rm = TRUE)
    ) %>%
    filter(datekey <= as.Date("2022-03-31"))
  
  monthendwl <- dailywl %>%
    filter(datekey == lastdayofmonth)
  
  ## Performance ----
  performanceData <- monthendwl %>%
    mutate(Cohort = case_when(
      Urgency %like% 'Cancer%' ~ 'Cancer'
      ,Urgency %like% 'Urgent%' ~ 'Urgent'
      ,Urgency %like% 'Routine%' ~ 'Routine'
    )) %>%
    group_by(Cohort,lastdayofmonth) %>%
    summarise(`0-18 Weeks` = sum(`0-18 Weeks`,na.rm = TRUE), TotalPTL = sum(TotalPTL, na.rm = TRUE)) %>%
    mutate(Performance = `0-18 Weeks`/TotalPTL)

  ## ROTT curve analysis ----
  rott_times <- attributes %>%
    filter(key == "ClockStop_ROTT"| key %like% "%Stop:ROTT") %>%
    group_by(name) %>%
    arrange(name, key) %>%
    mutate(rott_time = time - lag(time,1)) %>%
    filter(key != "ClockStop_ROTT") %>%
    arrange(rott_time,time) 
    
  ## Clock Stops ----
  modelClockStops <- attributes %>%
    filter(key %in% c('ClockStop_Treat','ClockStop_ROTT')) %>%
    left_join(adm_indicator, by = c("name")) %>%
    left_join(mastercal, by = c("time" = "timeindex")) %>%
    mutate(
      AdmittedInd = if_else(is.na(AdmittedInd),"NonAdmitted",AdmittedInd)
      ,Urgency = case_when(
        name %like% '%Cancer%' ~ 'Cancer'
        ,name %like% '%Urgent%' ~ 'Urgent'
        ,name %like% '%Routine%' ~ 'Routine'
      )
    ) %>%
    group_by(monthstarting,AdmittedInd,Urgency,key) %>%
    summarise(Stops = n())
  
  ## Debug formula ----
  debugformula <- monthendwl %>%
    group_by(lastdayofmonth) %>%
    summarise(TotalPTL = sum(TotalPTL,na.rm = TRUE)) %>%
    mutate(LastMonthPTL = lag(TotalPTL,1)) %>%
    filter(!is.na(LastMonthPTL)) %>%
    left_join(
      {
        clockStartsInmodel %>%
          group_by(monthstarting) %>%
          summarise(ClockStarts = sum(ClockStarts,na.rm = TRUE)) %>%
          mutate(lastdayofmonth = (monthstarting %m+% months(1))-1) %>%
          dplyr::select(-monthstarting)
      }
      ,by = c("lastdayofmonth")
    ) %>%
    left_join(
      {
        modelClockStops %>%
          group_by(monthstarting) %>%
          summarise(ClockStops = sum(Stops,na.rm = TRUE)) %>%
          mutate(lastdayofmonth = (monthstarting %m+% months(1))-1) %>%
          dplyr::select(-monthstarting) %>%
          filter(!is.na(lastdayofmonth))
      }
      ,by = c("lastdayofmonth")
    ) %>%
    mutate(
      valid = case_when(
        TotalPTL == LastMonthPTL + ClockStarts - ClockStops ~ TRUE
        ,TRUE ~ FALSE
      )
    )
  
  ## Collate all output types ----
  simulationEndTime <- Sys.time()
  
  simulationOutput <- list(
    iteration = i
    ,"parameters" = parameters
    ,"rawoutputs" = list(
      "resources" = resources
      ,"arrivals" = arrivals
      ,"attributes" = attributes
    )
    ,"tidyoutputs" = list(
      clockStartsInmodel = clockStartsInmodel
      ,clockStopsInModel = modelClockStops
      ,activityInModel = activityCheck
      ,monthEndWL = monthendwl
      ,performance = performanceData
      ,rott = rott_times
    )
    ,debug = debugformula
    ,"simulationDuration" = lubridate::as.duration(lubridate::interval(simulationStartTime,simulationEndTime))
  )
  
  # Return output ----
  simulationOutput
  
}


#### 12. Simulation Test Run ----
batchSimulation <- parallel::mclapply(1:niterations,function(x){runSimulation(x)},mc.cores = 8)

#### 13. Save raw simulation output to .RDS ----

#saveRDS(batchSimulation,file = paste0("/info_Rdev/1. Projects Development/ap2model/simOutputs/sim_",parameters$specialty,".rds"))

collatemonthendwl <- lapply(1:niterations,function(x){
  batchSimulation[[x]]$tidyoutputs$monthEndWL %>%
  mutate(iteration = batchSimulation[[x]]$iteration, specialty = parameters$specialty)}) 
collatemonthendwl <- data.table::rbindlist(collatemonthendwl)

collateclockstarts <- lapply(1:niterations,function(x){
  batchSimulation[[x]]$tidyoutputs$clockStartsInmodel %>%
    mutate(iteration = batchSimulation[[x]]$iteration, specialty = parameters$specialty)}) 
collateclockstarts <- data.table::rbindlist(collateclockstarts)

collateclockstops <- lapply(1:niterations,function(x){
  batchSimulation[[x]]$tidyoutputs$clockStopsInModel %>%
    mutate(iteration = batchSimulation[[x]]$iteration, specialty = parameters$specialty)}) 
collateclockstops <- data.table::rbindlist(collateclockstops)

collateclockstops %>%
  filter(key == "ClockStop_ROTT") %>%
  group_by(iteration,monthstarting) %>%
  summarise(Stops = sum(Stops)) %>%
  group_by(monthstarting) %>%
  summarise(MeanForecast = mean(Stops))

collateperformance <- lapply(1:niterations,function(x){
  batchSimulation[[x]]$tidyoutputs$performance %>%
    mutate(iteration = batchSimulation[[x]]$iteration, specialty = parameters$specialty)}) 
collateperformance <- data.table::rbindlist(collateperformance)

collateperformance %>%
  group_by(lastdayofmonth, iteration) %>%
  summarise(Performance = sum(`0-18 Weeks`, na.rm = TRUE)/sum(TotalPTL, na.rm = TRUE)) %>%
  ggplot(aes(x = lastdayofmonth, y = Performance, color = iteration, group = iteration)) +
  geom_line() + 
  ggtitle("Total RTT Performance")

collateperformance %>%
  group_by(lastdayofmonth, Cohort,iteration) %>%
  summarise(Performance = sum(`0-18 Weeks`, na.rm = TRUE)/sum(TotalPTL, na.rm = TRUE)) %>%
  ggplot(aes(x = lastdayofmonth, y = Performance, color = iteration, group = iteration)) +
  geom_line() +
  facet_wrap(vars(Cohort)) +
  ggtitle("Total RTT Performance by Cohort")

collateclockstops %>%
  group_by(monthstarting, iteration) %>%
  summarise(Stops = sum(Stops, na.rm = TRUE)) %>%
  ggplot(aes(x = monthstarting, y = Stops, color = iteration, group = iteration)) +
  geom_line() +
  ggtitle("Clock Stops")

collatemonthendwl %>%
  group_by(lastdayofmonth, iteration) %>%
  summarise(TotalPTL = sum(TotalPTL, na.rm = TRUE)) %>%
  ggplot(aes(x = lastdayofmonth, y = TotalPTL, color = iteration, group = iteration)) +
  geom_line() +
  ggtitle("Month End WL")

collatemonthendwl %>%
  mutate(AdmittedInd = if_else(is.na(AdmittedInd),"NonAdmitted",AdmittedInd)) %>%
  group_by(lastdayofmonth,AdmittedInd,iteration) %>%
  summarise(TotalPTL = sum(TotalPTL, na.rm = TRUE), NonBreach = sum(`0-18 Weeks`,na.rm = TRUE)) %>%
  ggplot(aes(x = lastdayofmonth, y = TotalPTL, color = iteration, group = iteration)) +
  geom_line() +
  facet_wrap(vars(AdmittedInd)) +
  ggtitle("Month End WL by Type")


sqlOutput_monthendwl <- collatemonthendwl %>%
  group_by(lastdayofmonth,iteration) %>%
  summarise(
    TotalPTL = sum(TotalPTL, na.rm = TRUE)
  ) %>%
  group_by(lastdayofmonth) %>%
  summarise(
    meanForecast = mean(TotalPTL,na.rm = TRUE)
    ,lower80 = quantile(TotalPTL,0.1)
    ,upper80 = quantile(TotalPTL,0.9)
    ,lower95 = quantile(TotalPTL,0.025)
    ,upper95 = quantile(TotalPTL,0.975)
  )

sqlOutput_performance <- collatemonthendwl %>%
  group_by(lastdayofmonth,iteration) %>%
  summarise(
    Performance = sum(`0-18 Weeks`, na.rm = TRUE)/sum(TotalPTL, na.rm = TRUE)
  ) %>%
  group_by(lastdayofmonth) %>%
  summarise(
    meanForecast = mean(Performance,na.rm = TRUE)
    ,lower80 = quantile(Performance,0.1)
    ,upper80 = quantile(Performance,0.9)
    ,lower95 = quantile(Performance,0.025)
    ,upper95 = quantile(Performance,0.975)
  )

sqlOutput_longwaiters <- collatemonthendwl %>%
  mutate(AdmittedInd = if_else(is.na(AdmittedInd),"NonAdmitted",AdmittedInd)) %>%
  group_by(lastdayofmonth,iteration,AdmittedInd) %>%
  summarise(
    LongWaiters = sum(`52-70 Weeks`, na.rm = TRUE) + sum(`70-104 Weeks`, na.rm = TRUE) + sum(`104+ Weeks`, na.rm = TRUE)
  ) %>%
  group_by(lastdayofmonth,AdmittedInd) %>%
  summarise(
    meanForecast = mean(LongWaiters,na.rm = TRUE)
    ,lower80 = quantile(LongWaiters,0.1)
    ,upper80 = quantile(LongWaiters,0.9)
    ,lower95 = quantile(LongWaiters,0.025)
    ,upper95 = quantile(LongWaiters,0.975)
  )


## Other code - example outputs, test plots etc ----
comparisondata <- runSQL(paste0("EXEC BI_REPORTING.Shiny.AP2_HindcastRTTPerformance @Specialty = '",parameters$specialty,"'"))
comparisondataset <- data.frame(
  month = unique(c(as.Date(comparisondata$MonthSub),as.Date(sqlOutput_monthendwl$lastdayofmonth)))
) %>%
  left_join(
    sqlOutput_monthendwl
    ,by = c("month"="lastdayofmonth")
  ) %>%
  left_join(
    comparisondata
    ,by = c("month"="MonthSub")
  ) 

comparisondataset %>%
  ggplot(aes(x = month, y = meanForecast)) +
  geom_line() +
  geom_line(aes(y = TotalPTL)) +
  geom_ribbon(aes(ymin = lower95, ymax = upper95), alpha = 0.4, fill = "blue")

comparisondataset2 <- data.frame(
  month = unique(c(as.Date(comparisondata$MonthSub),as.Date(sqlOutput_monthendwl$lastdayofmonth)))
) %>%
  left_join(
    sqlOutput_performance
    ,by = c("month"="lastdayofmonth")
  ) %>%
  left_join(
    comparisondata
    ,by = c("month"="MonthSub")
  ) %>%
  mutate(actualperformance = NonBreach/TotalPTL)

comparisondataset2 %>%
  ggplot(aes(x = month, y = meanForecast)) +
  geom_line() +
  geom_line(aes(y = actualperformance)) +
  geom_ribbon(aes(ymin = lower95, ymax = upper95), alpha = 0.4, fill = "blue")

sqlOutput_longwaiters %>%
  ggplot(aes(x = lastdayofmonth, y = meanForecast)) +
  geom_line()+
  geom_ribbon(aes(ymin = lower95, ymax = upper95), alpha = 0.2, fill = "blue") +
  facet_wrap(vars(AdmittedInd)) +
  ggtitle("Long Waiters")

processEndTime <- Sys.time()
print(paste0("Process duration: ",lubridate::as.duration(lubridate::interval(processStartTime,processEndTime))))


