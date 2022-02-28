## Pathway Derivation Program

library(infoPack)
library(dplyr)
library(simmer)
library(simmer.plot)

pathwayBuildStartTime <- Sys.time()

masterDataset <- runSQL("EXEC BI_REPORTING.Shiny.AP2_PathwayDetails_PercentileExclude")
masterDataset$ActivityOrder <- as.integer(masterDataset$ActivityOrder)
rottDataset <- runSQL("EXEC BI_REPORTING.Shiny.AP2_PathwayDetails_PercentileExclude_ROTTDelayPull")

## Function for randomisation ----
rollDice <- function(n){
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

rottCurveFx <- function(specialty,urgency,clocktype){
  
  rottData <- rottDataset %>%
    filter(Phase4AggregatedCode == specialty, PathwayUrgency == urgency, StartType == clocktype) 
    mutate(percentile85 = quantile(ROTTDelay,0.85)) %>%
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

rottDampeningFactor <- 0.4

## Create parent strings ----
specialtyDataset <- masterDataset %>%
  dplyr::select(
    ClockStart
    ,ClockStop
    ,PathwayUrgency
    ,StartType
    ,PathwayID
    ,PeriodID
    ,ActivitySpecialty
    ,ActivityOrder
    ,ActivityType
    ,Phase4AggregatedCode
    ,Phase4AggregatedDescription
  ) %>%
  mutate(ActivityChain = ActivityType) %>%
  ungroup() %>%
  mutate(uniqueID = row_number())

#Need a more efficient loop
# for(n in 1:as.numeric(max(specialtyDataset$ActivityOrder))){
#   specialtyDataset <- specialtyDataset %>%
#     group_by(PeriodID) %>%
#     mutate(ActivityChain = case_when(
#       ActivityOrder == n ~ paste0(lag(ActivityChain,1),'/',ActivityType)
#       ,TRUE ~ ActivityChain
#     ))
# }
for(n in 1:as.numeric(max(specialtyDataset$ActivityOrder))){
  updateActivity <- specialtyDataset %>%
    filter(ActivityOrder == n) %>%
    dplyr::select(PeriodID, uniqueID, ActivityOrder, ActivityType) %>%
    left_join(
      {specialtyDataset %>%
          filter(ActivityOrder == n-1) %>%
          dplyr::select(PeriodID, PrevActivityType = ActivityType)}
      ,by = c("PeriodID")
    ) %>%
    mutate(NewActivityType = paste0(PrevActivityType,'/',ActivityType)) %>%
    dplyr::select(uniqueID, NewActivityType)
  
  specialtyDataset <- specialtyDataset %>%
    left_join(updateActivity,c("uniqueID")) %>%
    mutate(ActivityType = if_else(!is.na(NewActivityType),NewActivityType,ActivityType)) %>%
    dplyr::select(-NewActivityType)
}

specialtyDataset <- specialtyDataset %>%
  group_by(PeriodID) %>%
  mutate(
    ParentString = lag(ActivityType,1)
    ,ChildString = ActivityType
  )

## Identify combinations ----
combinations <- runSQL("EXEC BI_REPORTING.Shiny.AP2_PathwayCombinations")
combinationsSubset <- combinations


## Create loop function ----

derivePathwayAndStore <- function(specialty,urgency,clocktype,subtrajectory = FALSE){
  
  edgeData <- specialtyDataset %>%
    filter(Phase4AggregatedCode == specialty, PathwayUrgency == urgency, StartType == clocktype) %>%
    filter(!is.na(ParentString),!is.na(ChildString)) %>%
    group_by(PathwayUrgency,StartType,ParentString,ChildString, ActivityOrder) %>%
    summarise(Instances = n()) %>%
    mutate(Instances = ifelse(ChildString %like% '%Stop:ROTT',as.integer(ceiling(rottDampeningFactor * Instances)),as.integer(Instances))) %>% #NEW
    group_by(PathwayUrgency,StartType,ParentString) %>%
    mutate(RunningSum = cumsum(Instances),GroupSum = max(cumsum(Instances)),Probability = RunningSum/GroupSum) %>%
    ungroup()
  
  chunksList <- unique(edgeData$ParentString)
  
  if(!subtrajectory){
    chunksList <- chunksList[chunksList=="Start"]
  }
  nChunks <- length(chunksList)
  
  chunkPathways <- lapply(
    1:nChunks
    ,function(x){
      currentChunk <- chunksList[x]
      
      edgeSubSet <- edgeData %>%
        filter(ParentString %like% paste0(currentChunk,"%"))
      
      trajectoryString <- paste0("trajectory() %>% set_attribute('Cohort: ",urgency,' ',clocktype,"',1) %>% @SUBBRANCH_",currentChunk,"@")
      steps <- edgeSubSet %>%
        mutate(Resource = 
                 case_when(
                   ChildString %like% "%/OP:N" ~ paste0("\n trajectory() %>% set_attribute('AdmittedInd',0) %>% seize('New_",PathwayUrgency,"') %>% set_global('attended_New_",PathwayUrgency,"_today',1,'+') %>% set_attribute('",ChildString,"',1) %>% set_attribute('Attended_OP:N',1) %>% timeout(1) %>% release('New_",PathwayUrgency,"') %>% @SUBBRANCH_")
                   ,ChildString %like% "%/OP:F" ~ paste0("\n trajectory() %>% set_attribute('AdmittedInd',0) %>% seize('Follow Up_",PathwayUrgency,"') %>% set_global('attended_Follow Up_",PathwayUrgency,"_today',1,'+')%>% set_attribute('",ChildString,"',1) %>% set_attribute('Attended_OP:F',1) %>% timeout(1) %>% release('Follow Up_",PathwayUrgency,"') %>% @SUBBRANCH_")
                   ,ChildString %like% "%/IP:DC" ~ paste0("\n trajectory() %>% set_attribute('AdmittedInd',1) %>% seize('Day Case_",PathwayUrgency,"') %>% set_global('attended_Day Case_",PathwayUrgency,"_today',1,'+')%>% set_attribute('",ChildString,"',1) %>% set_attribute('Attended_IP:DC',1) %>% timeout(1) %>% release('Day Case_",PathwayUrgency,"') %>% @SUBBRANCH_")
                   ,ChildString %like% "%/IP:EL IP" ~ paste0("\n trajectory() %>% set_attribute('AdmittedInd',1) %>% seize('Elective_",PathwayUrgency,"') %>% set_global('attended_Elective_",PathwayUrgency,"_today',1,'+')%>% set_attribute('",ChildString,"',1) %>% set_attribute('Attended_IP:EL IP',1) %>% timeout(1) %>% release('Elective_",PathwayUrgency,"') %>% @SUBBRANCH_")
                   ,ChildString %like% "%/Stop:Treat" ~ paste0("\n trajectory() %>% seize('ClockStop') %>% timeout(0) %>% release('ClockStop') %>% set_attribute('ClockStop_Treat',1) %>% set_attribute('",ChildString,"',1)")
                   ,ChildString %like% "%/Stop:ROTT" ~ paste0("\n trajectory() %>% seize('ReleaseROTTs') %>% timeout(0) %>% release('ReleaseROTTs') %>% set_attribute('Begin_ROTT_Period',1) %>% timeout(function(){rottCurveFx('",specialty,"','",urgency,"','",clocktype,"')}) %>% seize('ClockStop') %>% timeout(0) %>% release('ClockStop') %>% set_attribute('ClockStop_ROTT',1) %>% set_attribute('",ChildString,"',1)")
                 )
        )
      for(n in as.numeric(min(steps$ActivityOrder)):as.numeric(max(steps$ActivityOrder))){ 
        currentstep <- steps %>% 
          filter(ActivityOrder == n) %>%
          left_join(
            {steps %>%
                filter(ActivityOrder == n) %>%
                dplyr::select(ParentString) %>%
                unique() %>%
                mutate(SubGroup = row_number())}
            ,by = "ParentString"
          )
        
        #Added a step to remove clock stop childstrings if the first node in a partial trajectory
        if(subtrajectory && n == as.numeric(min(steps$ActivityOrder)) && n < as.numeric(max(steps$ActivityOrder))){
          currentstep <- filter(currentstep,!(ChildString %like% '%Stop:Treat%')) %>% ## no treatment stops, as these should already have taken effect if they are going to
            mutate(Instances = if_else(ChildString %like% '%Stop:ROTT%',as.integer(round(Instances * 0.2,0)),Instances)) ## allow ROTTs, but at a reduced rate - v4 for testing
        }
        
        nSubStep <- length(unique(currentstep$ParentString))
        for(o in 1:nSubStep){ 
          currentsubstep <- currentstep %>%
            filter(SubGroup == o) %>%
            mutate(subStepNumber = row_number())
          trajectoryString <- gsub(
            paste0("@SUBBRANCH_",currentsubstep$ParentString[1],"@") ## find the relevant sub branch to replace
            ,paste0(
              "branch(option = function(){rollDice("
              ,paste0("c(",paste0(as.numeric(currentsubstep$Instances),collapse = ","),")")
              ,")},"
              ,"continue = FALSE,"
              ,paste0(
                paste0(
                  currentsubstep$Resource 
                  ,if_else(currentsubstep$ChildString %like% '%Stop:ROTT'|currentsubstep$ChildString %like% '%Stop:Treat',"",as.character(currentsubstep$ChildString))
                  ,if_else(currentsubstep$ChildString %like% '%Stop:ROTT'|currentsubstep$ChildString %like% '%Stop:Treat',"","@")
                )
                ,collapse = ","
              )
              ,")"
            )
            ,trajectoryString
          )
        }
      }
      trajectoryStringParsed <- parse(text = trajectoryString)
      trajectory <- eval(trajectoryStringParsed)
      trajectory
    }
  )
  names(chunkPathways) <- chunksList
  chunkPathways
}

## for testing- limit to specialty specific pathways
combinationsSubset <- combinationsSubset %>%
  filter(GroupedSpecialtyCode == '101')

masterTrajectoriesList_v4a <- lapply(1:nrow(combinationsSubset),function(x){
  derivePathwayAndStore(
    combinationsSubset$GroupedSpecialtyCode[x]
    ,combinationsSubset$Urgency[x]
    ,combinationsSubset$PathwayType[x]
    ,FALSE
  )
})

masterTrajectoriesList_v4b <- lapply(1:nrow(combinationsSubset),function(x){
  derivePathwayAndStore(
    combinationsSubset$GroupedSpecialtyCode[x]
    ,combinationsSubset$Urgency[x]
    ,combinationsSubset$PathwayType[x]
    ,TRUE
  )
})



listnames <- paste0(combinationsSubset$GroupedSpecialtyCode,'_',combinationsSubset$Urgency,'_',combinationsSubset$PathwayType)
names(masterTrajectoriesList_v4a) <- listnames
names(masterTrajectoriesList_v4b) <- listnames

# plot(masterTrajectoriesList_v2a$`502_Cancer_New Pathway`$Start,verbose = TRUE)
# plot(masterTrajectoriesList_v2b$`502_Cancer_New Pathway`$Start,verbose = TRUE)
# plot(masterTrajectoriesList_v2b$`502_Cancer_New Pathway`$`Start/OP:N`,verbose = TRUE)

# plot(masterTrajectoriesList_v2$`502_Routine_New Pathway`$Start,verbose = TRUE)
# plot(masterTrajectoriesList_v2$`502_Routine_New Pathway`$`Start/IP:DC`,verbose = TRUE)
# plot(masterTrajectoriesList_v2$`502_Routine_New Pathway`$`Start/IP:DC/IP:DC`,verbose = TRUE)
# 
# masterTrajectoriesList_v2$`502_Cancer_New Pathway`

# plot(masterTrajectoriesList$`143_Routine_New Pathway`$Start)
# plot(masterTrajectoriesList$`330_Routine_Existing Pathway`$Start,verbose = TRUE)
# plot(masterTrajectoriesList$`191_Urgent_New Pathway`$Start,verbose = TRUE)
# plot(masterTrajectoriesList$`502_Cancer_New Pathway`$`Start/OP:N/OP:F`)
# 
# 
# trajectoryHost <- environment()
# trajectoryHost$masterTrajectoriesList <- masterTrajectoriesList
# 
# plot(trajectoryHost$masterTrajectoriesList$`330_Routine_Existing Pathway`$Start,verbose = TRUE)
# 
# saveRDS(trajectoryHost,file = "rdstest2.rds")
# trajectoryHost <- readRDS("rdstest2.rds")
# trajectoryHost$`100+_Cancer_Existing Pathway`$Start


pathwayBuildEndTime <- Sys.time()
print(paste0("Pathway build duration: ",lubridate::as.duration(lubridate::interval(pathwayBuildStartTime,pathwayBuildEndTime))))