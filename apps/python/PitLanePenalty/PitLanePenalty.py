# Pit lane penalty system for repeated track cutting.
#
# App displays a warning when you put more than 3 wheels out of the track. If you get more than 3 warnings,
# You must take a pit lane drive-through penalty. You cannot stop during the drive through for the penalty
# to count, so you cannot take your penalty while doing a normal pitstop.
#
# Pit lane penalties are announced to all players on the server via a chat message within the app.
#
# Wally Masterson, 28 Jan 2016
#
# V0.2
# - A cut now has to be 1.3 seconds or less in duration, and the track re-entry speed has to be 90% or more of the exit speed.
# - Only issues penalties in a race session, warnings in other sessions.
#
# V0.3
# - Shortened chat messages.
# - Made window smaller.
# - Log lap number for cuts, penalty given and taken
# - Only detects cuts in practice, qualifying and race modes.
#
# V0.4
# - Added laps to take penalty
#
# V0.5
# - Blink final warning and drive through penalty warning.
#
# V0.6
# - Display player's name in chat in the server log
#
# V0.7
# - Better cut detection for high-speed cuts (if over a certain percentage of max speed).
#
# V0.8
# - Reset warnings if race session is restarted.
# - Added invisible mode.
# V0.8A
# - Added chat messages if app is dismissed or activated from the app bar.
#
# V0.9
# - If you slow down to less than 90% of your exit speed at any point while off track, it's not a cut, no matter how fast you rejoin the track.
#
# V1.0
# - Now shows cuts in hotlap mode.
# - Flashes an "INVALID LAP, SLOW DOWN" warning for cuts in qualifying.
#
# V1.1
# - Added option for a penalty to be the addition of time to the final race result rather than a drive through penalty.
#
# V1.2
# - Added red/green track cut/safe indicator.
# - Made window appear briefly when activated.
# - Store car/track combination max speeds to make cut detection more accurate on 1st lap.
#
# V1.3
# - Use tyre dirt level as well to supplement the number of tyres off-track.
#
# V1.4
# - Reset warning counts if pit lane penalty is not taken, so further cuts attract new warnings
#
# V1.5
# - Added penalties for speeding in pit lane.
# - Added a 10 second (configurable) delay between cut track penalties.
#
# V1.6
# - Fixed for AC 1.3 (64 bit).
# - Now, pit lane penalties don't work 100% as designed, because sim_info.physics.sim_info.graphics.isInPitLane is only 1
#   when the limiter is actually on, not the whole time you're in pit lane.
#
# V1.7
# - Log what lap number a pit stop is taken on (the lap number when you enter pits), and how much fuel was added.
#
# V1.8
# - Allow for sim_info.graphics.isInPit not always being true if you're not quite in pits.
#
# V1.9
# - Reset variables when the session changes (resetSession).
# - Don't issue cuts after the race is over.
# - Better detection of car in pits.
# - Added optional start lights.
#
# V1.10
# - Make random start light interval the same for each player
#
# V1.11
# - Import ctypes *after* sys.path is set up.
# - You can't jump start until after the AC lights go out.
#
# V1.12
# - Only issue jump start warnings on lap 1.
# - Briefly show the start lights when the app is activated.
# - Hide the start lights in all sessions except for race.
#
# V1.13
# - Use inPitLane shared memory variable to detect when the car is in pit lane.
# - Added flag images for warnings and penalties.
#
# V1.14
# - Made setting light images more efficient - i.e. only do each stage once.
# - Allow for the AC 1.6+ bug where sessionTimeLift can go up by a few thousands of a second.
#
# V1.15
# - Added ENABLED_DAYS setting to disable all but cut track warnings on certain days.
#
# V1.15
# - Added PENALTY_MODE and PIT_LANE_SPEED to the output config message.
#
# V1.16
# - Allow for different config files for each day of the week, which will be used if they exist (e.g. "PLP-Sat.ini").
#   If no day-specific config file exists, PLP.ini will be used by default.
# - Added optional race start timer (counts up from race start until you move).
#   Enable this by setting raceCountupTimerEnabled=true in PLP.ini.
#
# V1.17
# - Don't get cuts in pit lane (e.g. at Nurburgring where the pit lane makes the tyres dirty).
# - Fixed fuel amount not showing when adding fuel in a pitstop.
#
# V1.18
# - Don't write to speed.ini until AC is shut down.
#
# V1.18a
# - Temporary hack so PLP continues to operate in a timed race.
#
# V1.19
# - Added AMNESTY_LAPS.
#
# V1.20
# - Added SHOW_CUTS_IN_SESSIONS.
#
# V1.21
# - Added ENABLED_SERVER_FILTER.
# - Renamed SimInfo to PLPSimInfo for extra isolation from other apps.
#
# V1.21a
# - Added SHOW_CUTS_IN_SESSIONS to the version chat.
#
# V1.22
# - Added separate SECONDS_PER_SPEEDING_PENALTY and SECONDS_PER_CUTTING_PENALTY settings.
#
# V1.23
# - Added separate PENALTY_MODE_CUTTING and PENALTY_MODE_SPEEDING.
#
# V1.24
# - Chat PLP version also when app is activated
#
# V1.25
# - Added CUT_INDICATOR_SIZE setting.
#
# V1.26/1.27
# - Added reading TOTAL_WARNINGS from server name

import time
import ac
import acsys
import os
import sys
import configparser
import traceback
import platform
import re
import datetime
import math

VERSION = "1.27"


class StartLightStep:
	off = 0
	shown = 1
	light1on = 2
	light2on = 3
	light3on = 4
	light4on = 5
	light5on = 6
	allLightsOff = 7
	lightsHidden = 8


TripleMode = False
try:
	if platform.architecture()[0] == "64bit":
		libdir = 'PLPlib/lib64'
	else:
		libdir = 'PLPlib/lib'
	sys.path.insert(0, os.path.join(os.path.dirname(__file__), libdir))
	os.environ['PATH'] = os.environ['PATH'] + ";."

	import ctypes

	import PLPlib.plp_sim_info

	sim_info = PLPlib.plp_sim_info.PLPSimInfo()

	# Check My Documents location
	from ctypes import wintypes

	CSIDL_PERSONAL = 5  # My Documents
	SHGFP_TYPE_CURRENT = 0  # Get default value
	buf = ctypes.create_unicode_buffer(ctypes.wintypes.MAX_PATH)
	ctypes.windll.shell32.SHGetFolderPathW(None, CSIDL_PERSONAL, None, SHGFP_TYPE_CURRENT, buf)

	# Check AC Resolution
	if os.path.isfile(buf.value + '/Assetto Corsa/cfg/video.ini'):
		videoconfig = configparser.ConfigParser()
		videoconfig.read(buf.value + '/Assetto Corsa/cfg/video.ini')
		Resolution = int(videoconfig['VIDEO']['WIDTH'])
		ResolutionHeight = int(videoconfig['VIDEO']['HEIGHT'])
		FullScreen = videoconfig.getboolean('VIDEO', 'FULLSCREEN')
		TripleMode = (videoconfig['CAMERA']['MODE'] == 'TRIPLE')
		ac.log('PLP: Resolution on video.ini: ' + str(Resolution))
		ac.log('PLP: FullScreen on video.ini: ' + str(FullScreen))
	else:
		Resolution = ctypes.windll.user32.GetSystemMetrics(0)
		ResolutionHeight = ctypes.windll.user32.GetSystemMetrics(1)
		ac.log('PLP: Resolution on SystemMetrics: ' + str(Resolution))
		FullScreen = True

except:
	ac.log(traceback.format_exc())

# Config
WHEELS_OUT = 3
MIN_SPEED = 50
WARNING_DURATION = 10
CHAT_DURATION = 10
TOTAL_WARNINGS = 3
ENABLE_PENALTIES = True
MAX_CUT_TIME = 1.3
MIN_SLOW_DOWN_RATIO = 0.9
LAPS_TO_TAKE_PENALTY = 3
MAX_SPEED_RATIO_FOR_CUT = 0.5
INVISIBLE_MODE = 0
PENALTY_MODE_CUTTING = 1
PENALTY_MODE_SPEEDING = 1
QUAL_SLOW_DOWN_SPEED = 50
SECONDS_PER_CUTTING_PENALTY = 10
SECONDS_PER_SPEEDING_PENALTY = 10
PIT_LANE_SPEED = 82
ENABLE_SPEEDING_PENALTIES = True
SECONDS_BETWEEN_CUTS = 10
USE_START_LIGHTS = True
USE_FLAG_IMAGES = True
FLAG_POS = "left"
JUMP_START_PENALTY_SECONDS = 0
ENABLED_DAYS = ""
AMNESTY_LAPS = 1
SHOW_CUTS_IN_SESSIONS = "0,1,2,3"
ENABLED_SERVER_FILTER = ""
CUT_INDICATOR_SIZE = 50

TEAM = 0
TEAM_CAR = 1

# Constants
SESSION_PRAC = 0
SESSION_QUAL = 1
SESSION_RACE = 2
SESSION_HOTLAP = 3
SESSION_TIME_ATTACK = 4
SESSION_DRIFT = 5
SESSION_DRAG = 6
PLP_CHAT = "PLP>"
PLP_TEAM_CHAT = "PLT>"
PLP_LOG = "PLP: "
CHAT_DELIM = '|'
WINDOW_WIDTH = 290
MARGIN = 5
FIRST_LINE_Y = 35
LINE_HEIGHT = 20
WINDOW_HEIGHT = FIRST_LINE_Y + LINE_HEIGHT * 2 + MARGIN
BLINK_INTERVAL = 1
PENALTY_MODE_DRIVETHRU = 1
PENALTY_MODE_TIME = 2
CURRENTLY_CUTTING_NOT = 0
CURRENTLY_CUTTING_YES = 1
CURRENTLY_CUTTING_SAFE = 2

appWindow = 0
numWarnings = 0
cutDetected = False
pitLanePenalty = False
speedingPenalty = False
takingPenalty = False
invalidQualLapWarning = False
penaltyVoid = False
penaltyMessageSent = False
versionChatSent = False
statusLabel = 0
warningLabel = 0
chatLabel = 0
timerLabel = 0
eraseWarningTime = 0
eraseChatTime = 0
gameTime = 0
lastCutTime = -WARNING_DURATION
lastIssuedCutTime = 0
startCutSpeed = 0
slowestOffTrackSpeed = 0
lastSession = -1
session = 0
configFailed = False
penaltyLapsLeft = 0
lastLap = 0
blinkStatus = False
statusBlinkShowing = True
nextStatusBlinkTime = 0
statusBlinkStopTime = 0
warningBlinkStopTime = 0
blinkWarning = False
warningBlinkShowing = True
nextWarningBlinkTime = 0
warningText = ""
playerName = ac.getDriverName(0)
maxSpeed = 0
lastSessionTimeLeft = 36000000
# 1 = Off track, might get a warning. 2 = Off track, won't get a warning.
currentlyCutting = 0
appWindowActivated = 0
showWindowTitle = False
lastdfl = 0
lastdfr = 0
lastdrl = 0
lastdrr = 0
speedingOnLap = 0
isInPitLaneOnLap = 0
lastIsInPitLane = False
isInPitLaneLap = False
lastIsInPitLaneLap = 0
speedingInPits = False
pitStartFuel = 0
wasInPit = False
PitX, PitY, PitZ = 0, 0, 0  # Pitbox co-ords
AppInitialised = False  # bool so can set app info on first run
appEnabled = True
raceTimerVisible = False
raceTimerRemoved = False
raceCountupTimerEnabled = False
sessionEnabled = True

raceSessionDuration = 0
startLight1 = 0
startLight2 = 0
startLight3 = 0
startLight4 = 0
startLight5 = 0
flagImageBW = 0
flagImageB = 0
windowX = 0
windowY = 0
lightsX = 0
lightsY = 0
flagX = 0
flagY = 0
startLightsOff = False
lightHoldSecs = 0
startLightColour = "Red"
jumpStartDetected = False
startLightsInited = False
DEFAULT_START_LIGHTS_START_TIME = 100000
LIGHT_WIDTH = 79
LIGHT_HEIGHT = 154
LIGHT_MARGIN = 20
FLAG_WIDTH = 120
FLAG_HEIGHT = 133
startLightsTempShown = False
startLightsShown = False
startLightStep = StartLightStep.off

startLightStartTime = DEFAULT_START_LIGHTS_START_TIME


def acMain(acVersion):
	global appWindow, warningLabel, chatLabel, timerLabel, statusLabel, configFailed, appWindowActivated, showWindowTitle
	global startLight1, startLight2, startLight3, startLight4, startLight5, Resolution, ResolutionHeight, lightsX, lightsY
	global flagImageBW, flagImageB, flagX, flagY, appEnabled, TripleMode

	configFailed = not readConfig()

	appEnabled = isEnabled(ENABLED_DAYS, ENABLED_SERVER_FILTER)

	appWindow = ac.newApp("Pit Lane Penalty")
	ac.setSize(appWindow, WINDOW_WIDTH, WINDOW_HEIGHT)
	ac.setIconPosition(appWindow, -1155, -1155)

	warningLabel = ac.addLabel(appWindow, "")
	ac.setPosition(warningLabel, MARGIN, FIRST_LINE_Y)

	statusLabel = ac.addLabel(appWindow, "")
	ac.setPosition(statusLabel, WINDOW_WIDTH - 100, FIRST_LINE_Y)

	chatLabel = ac.addLabel(appWindow, "")
	ac.setPosition(chatLabel, MARGIN, FIRST_LINE_Y + LINE_HEIGHT)

	timerLabel = ac.addLabel(appWindow, "")
	ac.setPosition(timerLabel, MARGIN, 0)
	ac.setFontSize(timerLabel, 72)

	if USE_FLAG_IMAGES:
		# Create penalty flag image
		# Top left corner of the middle screen
		if TripleMode:
			if FLAG_POS == "right":
				flagX = Resolution * 2 / 3 - FLAG_WIDTH - LIGHT_MARGIN
				flagY = LIGHT_MARGIN
			else:
				flagX = Resolution / 3 + LIGHT_MARGIN
				# Below other AC flags
				flagY = 105
		else:
			flagX = LIGHT_MARGIN

		flagImageBW = ac.addButton(appWindow, "")
		ac.setPosition(flagImageBW, 0, 0)
		ac.setSize(flagImageBW, FLAG_WIDTH, FLAG_HEIGHT)
		ac.drawBorder(flagImageBW, 0)
		ac.setVisible(flagImageBW, 0)
		ac.setBackgroundOpacity(flagImageBW, 0)
		ac.setBackgroundTexture(flagImageBW, "apps/python/PitLanePenalty" + IMG_FOLDER + "/BlackWhiteFlag.png")

		flagImageB = ac.addButton(appWindow, "")
		ac.setPosition(flagImageB, 0, 0)
		ac.setSize(flagImageB, FLAG_WIDTH, FLAG_HEIGHT)
		ac.drawBorder(flagImageB, 0)
		ac.setVisible(flagImageB, 0)
		ac.setBackgroundOpacity(flagImageB, 0)
		ac.setBackgroundTexture(flagImageB, "apps/python/PitLanePenalty" + IMG_FOLDER + "/BlackFlag.png")

	if USE_START_LIGHTS:
		# Create start lights
		# Top right corner of the middle screen
		if TripleMode:
			lightsX = Resolution * 2 / 3 - LIGHT_WIDTH * 5 - LIGHT_MARGIN
		else:
			lightsX = Resolution - LIGHT_WIDTH * 5 - LIGHT_MARGIN

		lightsY = LIGHT_MARGIN

		ac.log("PLP: lightsX,lightsY = {0},{1}".format(lightsX, lightsY))

		startLight1 = ac.addButton(appWindow, "")
		ac.setPosition(startLight1, 0, 0)
		ac.setSize(startLight1, LIGHT_WIDTH, LIGHT_HEIGHT)
		ac.drawBorder(startLight1, 0)
		ac.setVisible(startLight1, 0)
		ac.setBackgroundOpacity(startLight1, 0)
		ac.setBackgroundTexture(startLight1, "apps/python/PitLanePenalty" + IMG_FOLDER + "/LightOff.png")

		startLight2 = ac.addButton(appWindow, "")
		ac.setPosition(startLight2, LIGHT_WIDTH, 0)
		ac.setSize(startLight2, LIGHT_WIDTH, LIGHT_HEIGHT)
		ac.drawBorder(startLight2, 0)
		ac.setVisible(startLight2, 0)
		ac.setBackgroundOpacity(startLight2, 0)
		ac.setBackgroundTexture(startLight2, "apps/python/PitLanePenalty" + IMG_FOLDER + "/LightOff.png")

		startLight3 = ac.addButton(appWindow, "")
		ac.setPosition(startLight3, LIGHT_WIDTH * 2, 0)
		ac.setSize(startLight3, LIGHT_WIDTH, LIGHT_HEIGHT)
		ac.drawBorder(startLight3, 0)
		ac.setVisible(startLight3, 0)
		ac.setBackgroundOpacity(startLight3, 0)
		ac.setBackgroundTexture(startLight3, "apps/python/PitLanePenalty" + IMG_FOLDER + "/LightOff.png")

		startLight4 = ac.addButton(appWindow, "")
		ac.setPosition(startLight4, LIGHT_WIDTH * 3, 0)
		ac.setSize(startLight4, LIGHT_WIDTH, LIGHT_HEIGHT)
		ac.drawBorder(startLight4, 0)
		ac.setVisible(startLight4, 0)
		ac.setBackgroundOpacity(startLight4, 0)
		ac.setBackgroundTexture(startLight4, "apps/python/PitLanePenalty" + IMG_FOLDER + "/LightOff.png")

		startLight5 = ac.addButton(appWindow, "")
		ac.setPosition(startLight5, LIGHT_WIDTH * 4, 0)
		ac.setSize(startLight5, LIGHT_WIDTH, LIGHT_HEIGHT)
		ac.drawBorder(startLight5, 0)
		ac.setVisible(startLight5, 0)
		ac.setBackgroundOpacity(startLight5, 0)
		ac.setBackgroundTexture(startLight5, "apps/python/PitLanePenalty" + IMG_FOLDER + "/LightOff.png")

	appWindowActivated = time.clock()

	if INVISIBLE_MODE == 1:
		showWindowTitle = True

	ac.addOnChatMessageListener(appWindow, onChatMessage)
	ac.addOnAppDismissedListener(appWindow, onAppDismissed)
	ac.addOnAppActivatedListener(appWindow, onAppActivated)
	ac.addRenderCallback(appWindow, onFormRender)

	showApp()

	return "Pit Lane Penalty"


def showApp():
	global startLightsTempShown, startLightsShown, appEnabled

	if appEnabled:
		ac.setTitle(appWindow, "Pit Lane Penalty " + VERSION + " " + CFG_NAME)
	else:
		ac.setTitle(appWindow, "Pit Lane Penalty " + VERSION + " " + CFG_NAME + " - DISABLED")

	ac.setBackgroundOpacity(appWindow, 0.5)
	ac.drawBorder(appWindow, 1)
	# Temporarily show the start lights, to test if people can see them.
	# Don't show them temporarily in a race session though, so they don't confuse the start light sequence.
	if USE_START_LIGHTS and sim_info.graphics.session != SESSION_RACE:
		positionStartLights()

		ac.setBackgroundTexture(startLight1, "apps/python/PitLanePenalty" + IMG_FOLDER + "/LightRed.png")
		ac.setBackgroundTexture(startLight2, "apps/python/PitLanePenalty" + IMG_FOLDER + "/LightRed.png")
		ac.setBackgroundTexture(startLight3, "apps/python/PitLanePenalty" + IMG_FOLDER + "/LightRed.png")
		ac.setBackgroundTexture(startLight4, "apps/python/PitLanePenalty" + IMG_FOLDER + "/LightRed.png")
		ac.setBackgroundTexture(startLight5, "apps/python/PitLanePenalty" + IMG_FOLDER + "/LightRed.png")

		# Show the lights.
		ac.setVisible(startLight1, 1)
		ac.setVisible(startLight2, 1)
		ac.setVisible(startLight3, 1)
		ac.setVisible(startLight4, 1)
		ac.setVisible(startLight5, 1)

		startLightsTempShown = True
		startLightsShown = True


# Position the start lights, relative to the app window
def positionStartLights():
	global windowX, windowY

	windowX, windowY = ac.getPosition(appWindow)
	ac.log("PLP: windowX,windowY = {0},{1}".format(windowX, windowY))
	ac.setPosition(startLight1, lightsX - windowX, lightsY - windowY)
	ac.log("PLP: startLight1 at {0},{1}".format(lightsX - windowX, lightsY - windowY))
	ac.setPosition(startLight2, lightsX - windowX + LIGHT_WIDTH, lightsY - windowY)
	ac.setPosition(startLight3, lightsX - windowX + LIGHT_WIDTH * 2, lightsY - windowY)
	ac.setPosition(startLight4, lightsX - windowX + LIGHT_WIDTH * 3, lightsY - windowY)
	ac.setPosition(startLight5, lightsX - windowX + LIGHT_WIDTH * 4, lightsY - windowY)


def hideStartLights():
	global startLightsTempShown, startLightsShown

	ac.setVisible(startLight1, 0)
	ac.setVisible(startLight2, 0)
	ac.setVisible(startLight3, 0)
	ac.setVisible(startLight4, 0)
	ac.setVisible(startLight5, 0)
	startLightsTempShown = False
	startLightsShown = False


def onFormRender(deltaT):
	global showWindowTitle, startLightsTempShown

	# In invisible mode, show the app for 10 seconds so the user can see where it is on the screen.
	if showWindowTitle:
		if time.clock() - appWindowActivated > 10:
			# Now hide the window
			showWindowTitle = False
			ac.setTitle(appWindow, "")
			ac.setBackgroundOpacity(appWindow, 0)
			ac.drawBorder(appWindow, 0)

	if startLightsTempShown:
		if time.clock() - appWindowActivated > 5:
			# Hide the start lights
			if USE_START_LIGHTS and sim_info.graphics.session != SESSION_RACE:
				hideStartLights()

	# If speeding penalties are enabled, draw a green marker when the car is in pit lane, and you're not speeding.
	# Draw a red marker if you're in pit lane, and you are speeding.
	# If the car is currently cutting, and would get a penalty, draw a red marker.
	# If the car is currently cutting, but is safe from getting a penalty, draw a green marker.
	if currentlyCutting != CURRENTLY_CUTTING_NOT or ENABLE_SPEEDING_PENALTIES and sim_info.graphics.isInPitLane:
		if sim_info.graphics.isInPitLane and speedingInPits:
			ac.glColor4f(1, 0, 0, 1)
		elif sim_info.graphics.isInPitLane and not speedingInPits:
			ac.glColor4f(0, 1, 0, 1)
		elif currentlyCutting == CURRENTLY_CUTTING_YES:
			ac.glColor4f(1, 0, 0, 1)
		elif currentlyCutting == CURRENTLY_CUTTING_SAFE:
			ac.glColor4f(0, 1, 0, 1)
		if CUT_INDICATOR_SIZE == -1:
			indWidth = WINDOW_WIDTH - MARGIN
			indHeight = WINDOW_HEIGHT - MARGIN
		else:
			indWidth = CUT_INDICATOR_SIZE
			indHeight = CUT_INDICATOR_SIZE
		ac.glQuad(MARGIN, MARGIN, indWidth, indHeight)
		# ac.glQuad(MARGIN, MARGIN, 30, 30)

def acUpdate(deltaT):
	global numWarnings, cutDetected, eraseWarningTime, gameTime, lastCutTime, pitLanePenalty, takingPenalty, penaltyVoid, lastSession, penaltyMessageSent
	global eraseChatTime, session, startCutSpeed, versionChatSent, penaltyLapsLeft, lastLap, statusBlinkShowing, nextStatusBlinkTime, slowestOffTrackSpeed
	global warningText, statusBlinkStopTime, nextWarningBlinkTime, warningBlinkShowing, maxSpeed, lastSessionTimeLeft, invalidQualLapWarning, warningBlinkStopTime, warningLabel
	global currentlyCutting, lastdfl, lastdfr, lastdrl, lastdrr
	global speedingPenalty, speedingOnLap, isInPitLaneLap, lastIsInPitLane, speedingInPits, lastIssuedCutTime
	global lastIsInPitLaneLap, pitStartFuel, wasInPit
	global PitX, PitY, PitZ  # added global variables intiliased as 0,0,0. X,Y,Z co-ords of pit box
	global AppInitialised  # added global variable intiliased as False
	global raceSessionDuration, startLight1, startLight2, startLight3, startLight4, startLight5, appWindow, windowX, windowY, startLightsOff, startLightStartTime, lightHoldSecs
	global startLightColour, jumpStartDetected, startLightsInited, startLightsShown, startLightStep
	global raceTimerVisible, raceTimerRemoved, timerLabel
	global AMNESTY_LAPS, sessionEnabled

	if configFailed:
		ac.setFontColor(warningLabel, 1, 0, 0, 1)
		ac.setText(warningLabel, "Error reading config (see py_log.txt)")
		return

	# Record the car's initial pit position
	if not AppInitialised:  # First call to app, set variables
		if sim_info.graphics.session != SESSION_RACE or sim_info.graphics.isInPit:  # ideally want to set pit box position in quali or practice, could join a race session on the grid
			PitX, PitY, PitZ = ac.getCarState(0, acsys.CS.WorldPosition)
			ac.console("PLP: Pit position initialized at X:" + str(PitX) + " Y:" + str(PitY) + " Z:" + str(PitZ))
		AppInitialised = True

	gameTime += deltaT  # Seconds

	if not versionChatSent:
		# Dump out version and config info.
		sendChatLog(
			"running version {0}{13},{1}-{2}-{3}-{4}-{5}-{6}-{7}-{8}-{9}-{10}-{11}-{12}".format(VERSION, WHEELS_OUT, MIN_SPEED,
																					   TOTAL_WARNINGS, ENABLE_PENALTIES,
																					   MAX_CUT_TIME,
																					   MIN_SLOW_DOWN_RATIO,
																					   LAPS_TO_TAKE_PENALTY,
																					   PENALTY_MODE_CUTTING, PENALTY_MODE_SPEEDING, PIT_LANE_SPEED,
																					   AMNESTY_LAPS,
																					   SHOW_CUTS_IN_SESSIONS, CFG_NAME))
		versionChatSent = True

	# Get car info
	lap = sim_info.graphics.completedLaps + 1
	speed = ac.getCarState(0, acsys.CS.SpeedKMH)
	car_tyres_out = sim_info.physics.numberOfTyresOut
	if sim_info.graphics.isInPitLane and lastIsInPitLane == False:  # and sim_info.graphics.normalizedCarPosition > 0.5:

		# Send a team message when the car's pit limiter first comes on on this lap.
		if TEAM > 0 and lap != isInPitLaneLap:
			sendTeamChatMessage("Car {0} has entered pit lane".format(TEAM_CAR))

		# Keep track of what lap pit lane was entered, but only in the second half of the lap - i.e. when entering pits.
		# This makes sure the isInPitLaneLap is not reset if the pit limiter goes off and on again when driving down pit lane'
		# after the start line.
		isInPitLaneLap = lap

	lastIsInPitLane = sim_info.graphics.isInPitLane
	session = sim_info.graphics.session

	#
	# START LIGHTS
	#
	if USE_START_LIGHTS:
		if session == SESSION_RACE:
			raceSessionDuration += deltaT

			if int(ac.getCarState(0, acsys.CS.LapTime)) > 0 and startLightStartTime == DEFAULT_START_LIGHTS_START_TIME:
				# AC lights are out as soon as the lap time starts counting up. Start the PLP lights 1 second later.
				startLightStartTime = raceSessionDuration + 1
				startLightStep = StartLightStep.shown

			if raceSessionDuration > startLightStartTime + 6 + lightHoldSecs:
				# Hide the lights after they've been off for a second.
				if startLightStep == StartLightStep.allLightsOff:
					hideStartLights()
					startLightStep = StartLightStep.lightsHidden
			elif raceSessionDuration > startLightStartTime + 5 + lightHoldSecs:
				# Turn all lights off after holding them on for random lightHoldSecs seconds.
				if startLightStep == StartLightStep.light5on:
					ac.setBackgroundTexture(startLight1, "apps/python/PitLanePenalty" + IMG_FOLDER + "/LightOff.png")
					ac.setBackgroundTexture(startLight2, "apps/python/PitLanePenalty" + IMG_FOLDER + "/LightOff.png")
					ac.setBackgroundTexture(startLight3, "apps/python/PitLanePenalty" + IMG_FOLDER + "/LightOff.png")
					ac.setBackgroundTexture(startLight4, "apps/python/PitLanePenalty" + IMG_FOLDER + "/LightOff.png")
					ac.setBackgroundTexture(startLight5, "apps/python/PitLanePenalty" + IMG_FOLDER + "/LightOff.png")
					startLightsOff = True
					startLightStep = StartLightStep.allLightsOff
			elif raceSessionDuration > startLightStartTime + 4:
				if startLightStep == StartLightStep.light4on:
					ac.setBackgroundTexture(startLight5, "apps/python/PitLanePenalty" + IMG_FOLDER + "/Light" + startLightColour + ".png")
					startLightStep = StartLightStep.light5on
			elif raceSessionDuration > startLightStartTime + 3:
				if startLightStep == StartLightStep.light3on:
					ac.setBackgroundTexture(startLight4, "apps/python/PitLanePenalty" + IMG_FOLDER + "/Light" + startLightColour + ".png")
					startLightStep = StartLightStep.light4on
			elif raceSessionDuration > startLightStartTime + 2:
				if startLightStep == StartLightStep.light2on:
					ac.setBackgroundTexture(startLight3, "apps/python/PitLanePenalty" + IMG_FOLDER + "/Light" + startLightColour + ".png")
					startLightStep = StartLightStep.light3on
			elif raceSessionDuration > startLightStartTime + 1:
				if startLightStep == StartLightStep.light1on:
					ac.setBackgroundTexture(startLight2, "apps/python/PitLanePenalty" + IMG_FOLDER + "/Light" + startLightColour + ".png")
					startLightStep = StartLightStep.light2on
			elif raceSessionDuration > startLightStartTime:
				if startLightStep == StartLightStep.shown:
					ac.setBackgroundTexture(startLight1, "apps/python/PitLanePenalty" + IMG_FOLDER + "/Light" + startLightColour + ".png")
					startLightStep = StartLightStep.light1on
			elif raceSessionDuration > 0 and not startLightsInited:
				if startLightStep == StartLightStep.off:
					# Show the lights, relative to the app window
					positionStartLights()

					# The final red will be held for somewhere between 1 and 4 seconds.
					lightHoldSecs = rand(3.0) + 1
					ac.setBackgroundTexture(startLight1, "apps/python/PitLanePenalty" + IMG_FOLDER + "/LightOff.png")
					ac.setBackgroundTexture(startLight2, "apps/python/PitLanePenalty" + IMG_FOLDER + "/LightOff.png")
					ac.setBackgroundTexture(startLight3, "apps/python/PitLanePenalty" + IMG_FOLDER + "/LightOff.png")
					ac.setBackgroundTexture(startLight4, "apps/python/PitLanePenalty" + IMG_FOLDER + "/LightOff.png")
					ac.setBackgroundTexture(startLight5, "apps/python/PitLanePenalty" + IMG_FOLDER + "/LightOff.png")

					# Show the lights.
					ac.setVisible(startLight1, 1)
					ac.setVisible(startLight2, 1)
					ac.setVisible(startLight3, 1)
					ac.setVisible(startLight4, 1)
					ac.setVisible(startLight5, 1)

					startLightsInited = True
					startLightsShown = True
					startLightStep = StartLightStep.shown

			# You can't jump start until the AC lights go out (and the lap time starts counting up)
			# 1.12 - only issue warning on lap 1
			if int(ac.getCarState(0,
								  acsys.CS.LapTime)) > 0 and not startLightsOff and speed > 0.5 and not jumpStartDetected and lap == 1:
				# Jump Start - display yellow start lights.
				jumpStartDetected = True
				startLightColour = "Yellow"
				ac.setFontColor(warningLabel, 1, 1, 0, 1)
				ac.setText(warningLabel, "JUMP START")
				eraseWarningTime = gameTime + WARNING_DURATION
				issuePenalty("JUMP START", lap, JUMP_START_PENALTY_SECONDS)

	#
	# RACE TIMER
	#
	# LapTime becomes non-zero when AC lights go out.
	if raceCountupTimerEnabled:
		if session == SESSION_RACE and not raceTimerRemoved and int(ac.getCarState(0, acsys.CS.LapTime)) > 0:
			# Show the timer
			raceTimerVisible = True

			if speed > 3:
				# Once the car starts moving, remove and hide the race timer.
				raceTimerVisible = False
				raceTimerRemoved = True
				ac.setText(timerLabel, "")

		# Display the race timer value (the lap time)
		if raceTimerVisible:
			ac.setText(timerLabel, str(int(ac.getCarState(0, acsys.CS.LapTime) / 1000)))

	# Check for speeding in pit lane and issue a drive through penalty.
	if ENABLE_SPEEDING_PENALTIES:
		speedingInPits = sim_info.graphics.isInPitLane and speed > PIT_LANE_SPEED
		if speedingInPits:
			ac.console("speedingInPits is true")
		if session == SESSION_RACE and not speedingPenalty:
			# Check lap, in case driver speeds in pits a second time while already on a penalty
			# ac.console("lap = " + str(lap) + ", speedingOnLap = " + str(speedingOnLap))
			if not pitLanePenalty or lap != speedingOnLap:
				if speedingInPits:
					issuePenalty("SPEEDING", lap, SECONDS_PER_SPEEDING_PENALTY)
					speedingPenalty = True
					speedingOnLap = lap

	# Also check the tyres dirt level to see if any of them are off-track.
	dfl, dfr, drl, drr = sim_info.physics.tyreDirtyLevel
	dirty_tyres_out = 0
	# Check if tyre is dirty and getting dirtier.
	if dfl > 0 and dfl >= lastdfl:
		dirty_tyres_out = dirty_tyres_out + 1
	if dfr > 0 and dfr >= lastdfr:
		dirty_tyres_out = dirty_tyres_out + 1
	if drl > 0 and drl >= lastdrl:
		dirty_tyres_out = dirty_tyres_out + 1
	if drr > 0 and drr >= lastdrr:
		dirty_tyres_out = dirty_tyres_out + 1
	if dirty_tyres_out > car_tyres_out:
		car_tyres_out = dirty_tyres_out

	lastdfl = dfl
	lastdfr = dfr
	lastdrl = drl
	lastdrr = drr
	# ac.setText(chatLabel,"T{:.0f} {:.3f} {:.3f} {:.3f} {:.3f}, C{:.0f} D{:.0f}".format(sim_info.physics.numberOfTyresOut, dfl, dfr, drl, drr, car_tyres_out, dirty_tyres_out))
	# ac.setText(chatLabel, "{0}".format(sim_info.graphics.isInPitLane))

	# 1.17 - Tyres cannot be out in pit lane
	if sim_info.graphics.isInPitLane:
		car_tyres_out = 0

	sessionTimeLeft = sim_info.graphics.sessionTimeLeft
	if not math.isinf(sessionTimeLeft):
		# As of AC 1.6+, the sessionTimeLeft can go up and down a little bit, by about 0.004 to 0.008 seconds.
		# So give some allowance for timing "jitter", by adding 500 ms.
		if session == SESSION_RACE and sessionTimeLeft > lastSessionTimeLeft + 500:
			# Race has been restarted. Reset everything.
			resetWarnings()
			sessionEnabled = resetSession(session)
			raceStart()
		lastSessionTimeLeft = sessionTimeLeft

	if speed > maxSpeed:
		maxSpeed = speed

	if not (session == SESSION_HOTLAP or session == SESSION_PRAC or session == SESSION_QUAL or session == SESSION_RACE):
		ac.setText(warningLabel, "No cuts in this mode")
		return

	# 1.7, 1.8 Allow for sim_info.graphics.isInPit not always being true if you're not quite in pits.

	if PitX == 0 and sim_info.graphics.isInPit:  # set pit position correctly if not set before
		PitX, PitY, PitZ = ac.getCarState(0, acsys.CS.WorldPosition)
		ac.console("PLP: Pit position initialized later at X:" + str(PitX) + " Y:" + str(PitY) + " Z:" + str(PitZ))

	inPits = False
	if session == SESSION_RACE and speed < 2.5:
		# Stopped in a race.
		PosX, PosY, PosZ = ac.getCarState(0, acsys.CS.WorldPosition)  # current co-ord position
		delta = ((PosX - PitX) ** 2 + (PosY - PitY) ** 2 + (
			PosZ - PitZ) ** 2) ** 0.5  # straight line dist between pitbox and car
		if sim_info.graphics.isInPitLane and (
						delta < 4.0 or sim_info.graphics.isInPit):  # if InPit or within 8m of pitbox, quite relaxed limit guarantees app trigger on menu appear
			inPits = True

	# if sim_info.graphics.isInPitLane:
	#	ac.log(str(deltaT) + " inPits = " + str(inPits) + " speed = " + str(speed))

	# ac.setText(warningLabel,"inPits " + str(inPits) + " wasInPit " + str(wasInPit))

	if not inPits and wasInPit:
		# Pit stop has ended
		fuelDiff = sim_info.physics.fuel - pitStartFuel
		ac.console(
			str(deltaT) + " sim_info.physics.fuel = " + str(sim_info.physics.fuel) + ", fuelDiff = " + str(fuelDiff))
		if fuelDiff > 0.0:
			sendChatLog("Added {:.0f} litres".format(fuelDiff))
		wasInPit = False

	if inPits and isInPitLaneLap != lastIsInPitLaneLap:
		# Pit stop has started
		if TEAM > 0:
			sendTeamChatMessage(("Car {0} has pitted. GO!" + CHAT_DELIM + "lap {1}").format(TEAM_CAR, isInPitLaneLap))
		else:
			sendChatLog("Pitted on lap {0}".format(isInPitLaneLap))
		lastIsInPitLaneLap = isInPitLaneLap
		pitStartFuel = sim_info.physics.fuel
		ac.console(str(deltaT) + " pitStartFuel = " + str(pitStartFuel))
		wasInPit = True

	if lap != lastLap:
		# Starting a new lap
		# Make sure we don't count down a lap already, on the pitstop where the speeding occurred, when you cross the line
		# in pits (controlled by isInPitLaneLap).
		#  or (speedingPenalty and lap > speedingOnLap and isInPitLaneLap > speedingOnLap):
		if (PENALTY_MODE_CUTTING == PENALTY_MODE_DRIVETHRU or PENALTY_MODE_SPEEDING == PENALTY_MODE_DRIVETHRU) and (
					not speedingPenalty or speedingPenalty and not sim_info.graphics.isInPitLane):
			# Reduce the number of laps left to take a penalty.
			if pitLanePenalty and not takingPenalty:
				penaltyLapsLeft = penaltyLapsLeft - 1
				if penaltyLapsLeft == 0:
					# Start blinking the "this lap" text.
					startBlinkingStatus()
				elif penaltyLapsLeft < 0:
					penaltyLapsLeft = 0
					sendChatMessage("ignored penalty")
					# Reset warning counts so that further cuts attract further penalties.
					resetWarnings()
				setStatusText()
		lastLap = lap
		if invalidQualLapWarning:
			# Reset any invalid qualifying lap message at the start of a new lap.
			invalidQualLapWarning = False
			# Stop the blinking warning (see below).
			warningBlinkStopTime = 1

	# If driver slows down to QUAL_SLOW_DOWN_SPEED or enter the pits, stop the "Invalid Lap" warning.
	if invalidQualLapWarning and (speed <= QUAL_SLOW_DOWN_SPEED or sim_info.graphics.isInPitLane):
		invalidQualLapWarning = False
		# Stop the blinking warning (see below).
		warningBlinkStopTime = 1

	# Blink the status text.
	# Blink "This lap" when a penalty is due.
	# Blink the warning count when on the last warning.
	if blinkStatus and gameTime > nextStatusBlinkTime:
		if statusBlinkShowing:
			clearStatusText()
		else:
			setStatusText()
		statusBlinkShowing = not statusBlinkShowing
		nextStatusBlinkTime = gameTime + BLINK_INTERVAL  # seconds
		if 0 < statusBlinkStopTime < gameTime:
			setStatusText()
			# Stop blinking
			stopBlinkingStatus()

	# Blink the warning text.
	# Blink "DRIVE THROUGH PENALTY"
	if blinkWarning and gameTime > nextWarningBlinkTime:
		if warningBlinkShowing:
			warningText = ac.getText(warningLabel)
			ac.setText(warningLabel, "")
		else:
			ac.setText(warningLabel, warningText)
		warningBlinkShowing = not warningBlinkShowing
		nextWarningBlinkTime = gameTime + BLINK_INTERVAL  # seconds
		if 0 < warningBlinkStopTime < gameTime:
			ac.setText(warningLabel, "")
			# Stop blinking
			stopBlinkingWarning()

	if session != lastSession:
		# Session has changed - reset warnings
		resetWarnings()
		sessionEnabled = resetSession(session)
		if session == SESSION_RACE:
			raceStart()

			raceSessionDuration = 0
	lastSession = session

	# Clear any warning text after a certain number of seconds.
	if 0 < eraseWarningTime < gameTime:
		# If we are just clearing a cut track warning while a pit lane penalty is active,
		# reset the warning to the DRIVE THROUGH PENALTY warning.
		if pitLanePenalty:
			ac.setFontColor(warningLabel, 1, 0, 0, 1)
			ac.setText(warningLabel, "DRIVE THROUGH PENALTY")
		else:
			ac.setText(warningLabel, "")
			hideBlackWhiteFlag()
		eraseWarningTime = 0

	# Clear any chat message after a certain number of seconds.
	if 0 < eraseChatTime < gameTime:
		sendChatMessage("")
		eraseChatTime = 0

	# Process pit lane penalties
	if PENALTY_MODE_CUTTING == PENALTY_MODE_DRIVETHRU or PENALTY_MODE_SPEEDING == PENALTY_MODE_DRIVETHRU:
		if sim_info.graphics.isInPitLane:
			# Check that if a driver has a speeding in pit lane penalty, they take it the *next* lap,
			# not the lap that they were speeding on.
			if pitLanePenalty and not penaltyVoid and (
						not speedingPenalty or speedingPenalty and isInPitLaneLap > speedingOnLap):
				# Driver is taking a pit lane penalty.
				if speed > 0.3:
					# Car has not stopped
					ac.setFontColor(warningLabel, 1, 1, 0, 1)
					ac.setText(warningLabel, "Penalty being taken")
					eraseWarningTime = 0
					if not penaltyMessageSent:
						# Only send the chat message once at the start of the penalty
						sendChatMessage("taking penalty")
						penaltyMessageSent = True
					takingPenalty = True
				else:
					# Car has stopped in pit lane, probably because it is taking a normal pit stop.
					# This voids any pit lane penalty.
					ac.setFontColor(warningLabel, 1, 0, 0, 1)
					ac.setText(warningLabel, "DRIVE THROUGH PENALTY")
					eraseWarningTime = 0
					if not penaltyVoid:
						sendChatMessage("re-take penalty")
					takingPenalty = False
					penaltyVoid = True
		elif takingPenalty:
			# Not in pit lane any more.
			# Pit lane penalty has been taken.
			resetWarnings()
			sendChatMessage("taken penalty" + CHAT_DELIM + "on lap {0}".format(lap))
			stopBlinkingWarning()
		else:
			# Make sure the next pit lane drive through is processed after a voided one.
			penaltyVoid = False
			penaltyMessageSent = False

	# Stop detecting cuts after the race.
	# 1.9
	# 1.18a - temporarily comment this out for AC 1.12 and timed races
	# if session == SESSION_RACE and lap > sim_info.graphics.numberOfLaps:
	#	ac.setText(warningLabel,"Race over")
	#	return;
	if not pitLanePenalty and car_tyres_out > WHEELS_OUT:
		if not cutDetected:
			if speed > MIN_SPEED and gameTime > lastIssuedCutTime + SECONDS_BETWEEN_CUTS:
				# This is the start of a potentially cut track that is:
				#	- not while the driver is already a pit lane penalty notice
				#	- over a certain speed.
				lastCutTime = gameTime
				startCutSpeed = speed
				slowestOffTrackSpeed = speed
				cutDetected = True
				currentlyCutting = CURRENTLY_CUTTING_YES
		else:
			# Car is off track during a cut.
			# Keep track of the minimum speed while off track.
			if speed < slowestOffTrackSpeed:
				slowestOffTrackSpeed = speed

			# The conditions are that no penalty will be given (see cutting check below).
			if not ((gameTime - lastCutTime <= MAX_CUT_TIME or speed > maxSpeed * MAX_SPEED_RATIO_FOR_CUT) and speed / startCutSpeed > MIN_SLOW_DOWN_RATIO and slowestOffTrackSpeed / startCutSpeed > MIN_SLOW_DOWN_RATIO):
				currentlyCutting = CURRENTLY_CUTTING_SAFE
	elif car_tyres_out == 0:
		# No cut
		if cutDetected:
			# A cut is over
			# ac.setText(chatLabel,"{:.2f} {:.0f}/{:.0f}".format(gameTime - lastCutTime,speed,maxSpeed))
			# ac.setText(chatLabel,"{:.0f} {:.0f} {:.0f} {:.2f}".format(startCutSpeed,slowestOffTrackSpeed,speed,slowestOffTrackSpeed/startCutSpeed))
			if sessionEnabled \
					and (session != SESSION_RACE or lap > AMNESTY_LAPS) \
					and (gameTime - lastCutTime <= MAX_CUT_TIME or speed > maxSpeed * MAX_SPEED_RATIO_FOR_CUT) \
					and speed / startCutSpeed > MIN_SLOW_DOWN_RATIO \
					and slowestOffTrackSpeed / startCutSpeed > MIN_SLOW_DOWN_RATIO:
				# The cut took less than MAX_CUT_TIME seconds, or it was a fast cut, and the end speed was still more than 90% of the start speed.
				# Only count cut warnings if not race or beyond the number of amnesty laps in a race session.
				# In addition, if the car slowed to less than 90% of the start speed while off track, don't report a cut.
				numWarnings += 1
				lastIssuedCutTime = gameTime
				stopBlinkingStatus()
				setStatusText()
				if ENABLE_PENALTIES and session == SESSION_RACE and numWarnings > TOTAL_WARNINGS:
					if appEnabled:
						# Too many warnings in a race session - driver receives a penalty.
						issuePenalty("CUTTING", lap, SECONDS_PER_CUTTING_PENALTY)
				elif session == SESSION_QUAL:
					if appEnabled:
						# A cut during QUALIFYING - warn that the lap should be invalidated.
						invalidQualLapWarning = True
						ac.setFontColor(warningLabel, 1, 1, 0, 1)
						ac.setText(warningLabel, "INVALID LAP, SLOW DOWN")
						sendChatLog("Cut the track on qual lap")
						# Blink "forever". Slowing down to QUAL_SLOW_DOWN_SPEED will stop this, or starting the next lap.
						warningBlinkStopTime = gameTime + 10000  # seconds
						startBlinkingWarning()
				else:
					# Display track cut warning
					ac.setFontColor(warningLabel, 1, 1, 0, 1)
					ac.setText(warningLabel, "CUT TRACK WARNING")
					eraseWarningTime = gameTime + WARNING_DURATION
					showBlackWhiteFlag()
					sendChatLog("Cut the track on lap {0}".format(lap))
					if numWarnings == TOTAL_WARNINGS:
						# On the final warning. Blink the warning count for 30 seconds.
						statusBlinkStopTime = gameTime + 30  # seconds
						startBlinkingStatus()
		cutDetected = False
		currentlyCutting = CURRENTLY_CUTTING_NOT

	# Reset opacity in case app was moved (but not when we're temporarily showing the title).
	if INVISIBLE_MODE == 1 and not showWindowTitle:
		ac.setBackgroundOpacity(appWindow, 0)
		ac.drawBorder(appWindow, 0)


def showBlackWhiteFlag():
	showFlag(flagImageBW)


def hideBlackWhiteFlag():
	if flagImageBW != 0:
		ac.setVisible(flagImageBW, 0)


def showBlackFlag():
	showFlag(flagImageB)


def showFlag(flagID):
	global windowX, windowY

	if flagID != 0:
		# Reposition the flag every time in case the window has moved.
		windowX, windowY = ac.getPosition(appWindow)
		offset = 0
		if startLightsShown and FLAG_POS == "right":
			# If the flags are on the right, put them under the PLP start lights if shown.
			offset = LIGHT_HEIGHT + LIGHT_MARGIN
		ac.setPosition(flagID, flagX - windowX, flagY - windowY + offset)
		ac.setVisible(flagID, 1)


def hideBlackFlag():
	if flagImageB != 0:
		ac.setVisible(flagImageB, 0)


def issuePenalty(reason, lap, seconds):
	global warningBlinkStopTime, pitLanePenalty, penaltyLapsLeft, numWarnings, eraseWarningTime, gameTime

	ac.setFontColor(warningLabel, 1, 0, 0, 1)
	if reason == "CUTTING" and PENALTY_MODE_CUTTING == PENALTY_MODE_DRIVETHRU \
		or reason == "SPEEDING" and PENALTY_MODE_SPEEDING == PENALTY_MODE_DRIVETHRU:
		# Blink "forever", or until penalty is taken.
		warningBlinkStopTime = gameTime + 10000  # seconds
		ac.setText(warningLabel, "DRIVE THROUGH PENALTY")
		showBlackFlag()
		sendChatLog(("DRIVE THROUGH PENALTY FOR {0}" + CHAT_DELIM + "on lap {1}").format(reason, lap))
		pitLanePenalty = True
		penaltyLapsLeft = LAPS_TO_TAKE_PENALTY
	else:
		ac.setText(warningLabel, "{0} SECOND PENALTY".format(seconds))
		warningBlinkStopTime = gameTime + 30  # seconds
		sendChatLog(
			("GIVEN A {0} SECOND TIME PENALTY FOR {1}" + CHAT_DELIM + "on lap {2}").format(seconds, reason, lap))
		if reason == "CUTTING":
			# Reset the warning count
			numWarnings = 0
	eraseWarningTime = 0
	stopBlinkingStatus()
	setStatusText()
	startBlinkingWarning()


def startBlinkingStatus():
	global blinkStatus, statusBlinkShowing, nextStatusBlinkTime

	blinkStatus = True
	if blinkWarning:
		# If the warning is blinking, keep the two in synch.
		nextStatusBlinkTime = nextWarningBlinkTime
		statusBlinkShowing = warningBlinkShowing
	else:
		nextStatusBlinkTime = gameTime + BLINK_INTERVAL  # seconds
		statusBlinkShowing = True


def stopBlinkingStatus():
	global statusBlinkStopTime, blinkStatus, statusBlinkShowing, nextStatusBlinkTime

	statusBlinkStopTime = 0
	blinkStatus = False
	statusBlinkShowing = True
	nextStatusBlinkTime = 0


def startBlinkingWarning():
	global blinkWarning, warningBlinkShowing, nextWarningBlinkTime

	blinkWarning = True
	warningBlinkShowing = True
	nextWarningBlinkTime = gameTime + BLINK_INTERVAL  # seconds


def stopBlinkingWarning():
	global blinkWarning, warningBlinkShowing, nextWarningBlinkTime

	blinkWarning = False
	warningBlinkShowing = True
	nextWarningBlinkTime = 0


# Prefix chat messages sent through the app so that we only display PLP chat messages and no others.
def sendChatMessage(message):
	global eraseChatTime
	if not appEnabled:
		return
	ac.sendChatMessage(PLP_CHAT + message + CHAT_DELIM + playerName)
	eraseChatTime = gameTime + CHAT_DURATION


# Send a chat message visible only to your team
def sendTeamChatMessage(message):
	global eraseChatTime
	if not appEnabled:
		return
	ac.sendChatMessage(PLP_TEAM_CHAT + str(TEAM) + ": " + message)
	eraseChatTime = gameTime + CHAT_DURATION


# Write a chat message to the log only, not to the app.
def sendChatLog(message):
	if not appEnabled:
		return
	ac.sendChatMessage(PLP_LOG + message + CHAT_DELIM + playerName)


# Chat message handler
def onChatMessage(message, author):
	teamMessage = False

	if message.find(PLP_CHAT) == 0 or message.find(PLP_TEAM_CHAT) == 0:
		# Only display PLP chat or team chat prefixed messages
		# Remove the PLP marker
		strippedMessage = message.replace(PLP_CHAT, "", 1)
		strippedMessage = strippedMessage.replace(PLP_TEAM_CHAT, "", 1)

		# See if this is a team message for this team
		matchObj = re.match('(\d+): (.+)', strippedMessage, re.M | re.I)
		if matchObj:
			# This is a team message
			msgTeam = matchObj.group(1)
			if int(msgTeam) != TEAM:
				# Not for this team.
				return
			teamMessage = True
			strippedMessage = matchObj.group(2)
			# Check which team car this message came from
			matchObj = re.match('Car (\d+) .*', strippedMessage, re.M | re.I)
			fromCar = 0
			if matchObj:
				fromCar = int(matchObj.group(1))
			if fromCar == TEAM_CAR:
				# This message came from this car itself, so don't show it.
				return

		# Only display up to the delimiter.
		# This allows extra information to go into the log but not be displayed in the app.
		delimPos = strippedMessage.find(CHAT_DELIM)
		if delimPos >= 0:
			strippedMessage = strippedMessage[:delimPos]
		# Add the sender if there is some message text
		if len(strippedMessage) > 0 and not teamMessage:
			strippedMessage = author + " " + strippedMessage
		ac.setText(chatLabel, strippedMessage)


def onAppActivated(deltaT):
	global appWindowActivated, showWindowTitle, versionChatSent

	# Comment this out or you lose the version chat due to AC chat throttling
	# sendChatLog("app activated")
	versionChatSent = False
	showApp()
	appWindowActivated = time.clock()
	if INVISIBLE_MODE == 1:
		showWindowTitle = True


def onAppDismissed(deltaT):
	sendChatLog("app dismissed")


# Display the warning status in a race session.
def setStatusText():
	if session == SESSION_RACE:
		if ENABLE_PENALTIES:
			if pitLanePenalty:
				# Show how many laps left to take the penalty.
				if penaltyLapsLeft > 1:
					ac.setText(statusLabel, "{0} laps left".format(penaltyLapsLeft))
				elif penaltyLapsLeft == 1:
					ac.setText(statusLabel, "{0} lap left".format(penaltyLapsLeft))
				else:
					ac.setText(statusLabel, "THIS LAP")
			else:
				ac.setText(statusLabel, "Warnings: {0}/{1}".format(numWarnings, TOTAL_WARNINGS))
		else:
			ac.setText(statusLabel, "Warnings: {0}".format(numWarnings))


def clearStatusText():
	ac.setText(statusLabel, "")


# Reset everything after a penalty is taken or on session change.
def resetWarnings():
	global takingPenalty, pitLanePenalty, penaltyVoid, numWarnings, penaltyMessageSent, penaltyLapsLeft, blinkStatus, statusBlinkShowing, nextStatusBlinkTime, invalidQualLapWarning, speedingPenalty
	global warningLabel

	takingPenalty = False
	invalidQualLapWarning = False
	pitLanePenalty = False
	speedingPenalty = False
	penaltyVoid = False
	penaltyMessageSent = False
	numWarnings = 0
	penaltyLapsLeft = 0
	ac.setText(warningLabel, "")
	blinkStatus = False
	statusBlinkShowing = True
	nextStatusBlinkTime = 0
	hideBlackFlag()
	hideBlackWhiteFlag()
	setStatusText()


# Reset things when the session changes (or is restarted)
# Returns True or False if cuts are enabled in the current session or not.
def resetSession(l_session):
	global lastLap, lastIsInPitLane, lastIsInPitLaneLap, wasInPit, isInPitLaneLap, speedingOnLap, startLightsTempShown, raceTimerVisible, raceTimerRemoved

	lastLap = 0
	lastIsInPitLane = False
	lastIsInPitLaneLap = 0
	wasInPit = False
	isInPitLaneLap = 0
	speedingOnLap = 0
	raceTimerVisible = False
	raceTimerRemoved = False
	ac.setText(timerLabel, "")

	# Don't hide the lights when they are temporarily displayed when the app is activated.
	if USE_START_LIGHTS and not startLightsTempShown:
		hideStartLights()

	return isEnabledSession(l_session)


def raceStart():
	global raceSessionDuration, startLightsOff, startLightColour, jumpStartDetected, startLightStartTime, startLightsInited, startLightStep

	raceSessionDuration = 0
	startLightsOff = False
	startLightColour = "Red"
	jumpStartDetected = False
	startLightStartTime = DEFAULT_START_LIGHTS_START_TIME
	startLightsInited = False
	startLightStep = StartLightStep.off


# Returns true if the app should be enabled today, based on the comma separated list of valid days in enabledDays.
def isEnabledDay(enabledDays):
	if not enabledDays:
		# Enabled on every day
		return True

	# Check all the enabled days (comma delimited)
	today = str(datetime.datetime.today().weekday())
	for d in enabledDays.split(','):
		if today == d:
			return True

	return False


# Returns true if the app should be enabled (by day and/or server name)
def isEnabled(enabledDays, enabledServerFilter):
	if not enabledDays and not enabledServerFilter:
		# Always enabled
		return True

	# Check all the enabled days (comma delimited)
	dayEnabled = False
	if enabledDays:
		today = str(datetime.datetime.today().weekday())
		for d in enabledDays.split(','):
			if today == d:
				dayEnabled = True
				break
	else:
		# Enabled on all days.
		dayEnabled = True

	# Check the server name (comma delimited, case insensitive)
	serverEnabled = False
	if enabledServerFilter:
		for name in enabledServerFilter.split(','):
			if name.upper() in ac.getServerName().upper():
				serverEnabled = True
				break
	else:
		# Enabled on all servers.
		serverEnabled = True

	return dayEnabled and serverEnabled


# Returns true if cuts are shown in the given session.
def isEnabledSession(l_session):
	global SHOW_CUTS_IN_SESSIONS

	if not SHOW_CUTS_IN_SESSIONS:
		# Show cuts in each session if not set
		return True

	for s in SHOW_CUTS_IN_SESSIONS.split(','):
		if str(l_session) == s:
			return True

	return False


# Read settings from PLP.ini.
def readConfig():
	global CFG_NAME, IMG_FOLDER, WHEELS_OUT, MIN_SPEED, WARNING_DURATION, CHAT_DURATION, TOTAL_WARNINGS, ENABLE_PENALTIES, LAPS_TO_TAKE_PENALTY, MAX_CUT_TIME, MIN_SLOW_DOWN_RATIO, MAX_SPEED_RATIO_FOR_CUT, INVISIBLE_MODE
	global QUAL_SLOW_DOWN_SPEED, PENALTY_MODE_CUTTING, PENALTY_MODE_SPEEDING, SECONDS_PER_CUTTING_PENALTY, SECONDS_PER_SPEEDING_PENALTY, ENABLE_SPEEDING_PENALTIES, PIT_LANE_SPEED, SECONDS_BETWEEN_CUTS
	global maxSpeed
	global TEAM, TEAM_CAR
	global USE_START_LIGHTS, JUMP_START_PENALTY_SECONDS, USE_FLAG_IMAGES, FLAG_POS, ENABLED_DAYS, AMNESTY_LAPS, raceCountupTimerEnabled, SHOW_CUTS_IN_SESSIONS, ENABLED_SERVER_FILTER
	global CUT_INDICATOR_SIZE

	# If the server name ends with P6, set TOTAL_WARNINGS to 6.
	# Otherwise, use the value in the PLP.ini file.
	totalWarningsServer = False
	serverName = ac.getServerName().upper()
	m = re.search(".*P([0-9]+)$", serverName)
	if m:
		TOTAL_WARNINGS = int(m.group(1))
		totalWarningsServer = True

	try:
		# See if we have a config file for today. If it exists, use that file.
		today = datetime.datetime.today().weekday()
		daySuffix = ['Mon', 'Tue', 'Wed', 'Thu', 'Fri', 'Sat', 'Sun'][today]
		configFolder = "apps/python/PitLanePenalty/config/"
		configPath = ''

		for folder in os.listdir(configFolder):
			path = configFolder + folder + "/PLP-" + daySuffix + ".ini"

			if os.path.isfile(path):
				configPath = path

		if not configPath:
			configPath = configFolder + "PLP.ini"

		Config = configparser.ConfigParser()
		Config.read(configPath)

		# General settings.
		CFG_NAME = Config.get('General', 'CFG_NAME')
		IMG_FOLDER = Config.get('General', 'IMG_FOLDER')
		WHEELS_OUT = Config.getint('General', 'WHEELS_OUT')
		MIN_SPEED = Config.getint('General', 'MIN_SPEED')
		WARNING_DURATION = Config.getint('General', 'WARNING_DURATION')
		CHAT_DURATION = Config.getint('General', 'CHAT_DURATION')
		if not totalWarningsServer: TOTAL_WARNINGS = Config.getint('General', 'TOTAL_WARNINGS')
		ENABLE_PENALTIES = Config.getboolean('General', 'ENABLE_PENALTIES')
		LAPS_TO_TAKE_PENALTY = Config.getint('General', 'LAPS_TO_TAKE_PENALTY')
		CUT_INDICATOR_SIZE = Config.getint('General', 'CUT_INDICATOR_SIZE')
		INVISIBLE_MODE = Config.getint('General', 'INVISIBLE_MODE')
		PENALTY_MODE_CUTTING = Config.getint('General', 'PENALTY_MODE_CUTTING')
		PENALTY_MODE_SPEEDING = Config.getint('General', 'PENALTY_MODE_SPEEDING')
		ENABLE_SPEEDING_PENALTIES = Config.getboolean('General', 'ENABLE_SPEEDING_PENALTIES')
		PIT_LANE_SPEED = Config.getint('General', 'PIT_LANE_SPEED')
		SECONDS_BETWEEN_CUTS = Config.getint('General', 'SECONDS_BETWEEN_CUTS')
		USE_START_LIGHTS = Config.getboolean('General', 'USE_START_LIGHTS')
		USE_FLAG_IMAGES = Config.getboolean('General', 'USE_FLAG_IMAGES')
		FLAG_POS = Config.get('General', 'FLAG_POS')
		JUMP_START_PENALTY_SECONDS = Config.getint('General', 'JUMP_START_PENALTY_SECONDS')
		ENABLED_DAYS = Config.get('General', 'ENABLED_DAYS')
		AMNESTY_LAPS = Config.getint('General', 'AMNESTY_LAPS')
		SHOW_CUTS_IN_SESSIONS = Config.get('General', 'SHOW_CUTS_IN_SESSIONS')
		ENABLED_SERVER_FILTER = Config.get('General', 'ENABLED_SERVER_FILTER')

		ENABLE_RACE_COUNTUP_TIMER_DAYS = Config.get('General', 'ENABLE_RACE_COUNTUP_TIMER_DAYS')
		# If setting is not present, disable it on all days.
		if not ENABLE_RACE_COUNTUP_TIMER_DAYS:
			ENABLE_RACE_COUNTUP_TIMER_DAYS = "Disabled"
		raceCountupTimerEnabled = isEnabledDay(ENABLE_RACE_COUNTUP_TIMER_DAYS)

		# Disable some settings on days and servers when the app is disabled
		if not isEnabled(ENABLED_DAYS, ENABLED_SERVER_FILTER):
			USE_START_LIGHTS = False
			ENABLE_SPEEDING_PENALTIES = False

		# Team settings.
		TEAM = Config.getint('Teams', 'TEAM')
		TEAM_CAR = Config.getint('Teams', 'TEAM_CAR')

		# FineTuning settings.
		MAX_CUT_TIME = Config.getfloat('FineTuning', 'MAX_CUT_TIME')
		MIN_SLOW_DOWN_RATIO = Config.getfloat('FineTuning', 'MIN_SLOW_DOWN_RATIO')
		MAX_SPEED_RATIO_FOR_CUT = Config.getfloat('FineTuning', 'MAX_SPEED_RATIO_FOR_CUT')
		QUAL_SLOW_DOWN_SPEED = Config.getfloat('FineTuning', 'QUAL_SLOW_DOWN_SPEED')
		SECONDS_PER_CUTTING_PENALTY = Config.getint('FineTuning', 'SECONDS_PER_CUTTING_PENALTY')
		SECONDS_PER_SPEEDING_PENALTY = Config.getint('FineTuning', 'SECONDS_PER_SPEEDING_PENALTY')

	except:
		ac.log(traceback.format_exc())
		return False

	# Read the recorded max speed for this car/track combo.
	try:
		Config.read("apps/python/PitLanePenalty/speed.ini")
		maxSpeed = Config.getfloat('MaxSpeed', ac.getCarName(0) + ac.getTrackName(0) + ac.getTrackConfiguration(0))
	except:
		# File or speed doesn't exist yet.
		maxSpeed = 0

	return True


def acShutdown(*args):
	writeSpeedConfig()


# Write a new max speed to speed.ini for the current car/track.
def writeSpeedConfig():
	global maxSpeed

	Config = configparser.ConfigParser()
	try:
		Config.read("apps/python/PitLanePenalty/speed.ini")
	except:
		# Do nothing - file will be created.
		ac.log("Pit Lane Penalty: creating speed.ini")

	section = 'MaxSpeed'
	# Add the section if it doesn't exist yet.
	if section not in Config.sections():
		Config.add_section(section)

	Config.set(section, ac.getCarName(0) + ac.getTrackName(0) + ac.getTrackConfiguration(0), "{:.1f}".format(maxSpeed))
	with open('apps/python/PitLanePenalty/speed.ini', 'w+') as configfile:
		Config.write(configfile)


# Return a random number between [0 and range) which is the same for each player.
def rand(in_range):
	# Invariants for each player
	a = int(len(ac.getTrackName(0)))
	b = int(sim_info.graphics.numberOfLaps)
	c = int(datetime.datetime.now().day)

	seed = a * b * c
	r = (((seed * 1103515245 + 12345) & 0x7FFFFFFF) / float(0x80000000)) * in_range

	return r
