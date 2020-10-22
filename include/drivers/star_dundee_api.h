/*
 * This is a part of PolyORB-HI-C distribution, a minimal
 * middleware written for generated code from AADL models.
 * You should use it with the Ocarina toolsuite.
 *
 * For more informations, please visit http://www.openaadl.org
 *
 * Copyright (C) 2018-2019 ESA & ISAE, 2019-2020 OpenAADL
 */

#ifndef __STAR_DUNDEE_API_H__
#define __STAR_DUNDEE_API_H__

/* Wrapper for Star Dundee Mk3 API */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <stddef.h>
#include "star-api.h"
#include "star-dundee_types.h"

/** Send message through selectedChannel */
size_t dundee_sending(void* message, int message_size, STAR_CHANNEL_ID selectedChannel);

/** Receive message through selectedChannel */
size_t dundee_receiving(void* message, STAR_CHANNEL_ID selectedChannel);

#endif /*__STAR_DUNDEE_API_H__ */
