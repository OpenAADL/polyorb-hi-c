/* GRSPW Packet driver Library helper functions */

#ifndef __GRSPW_PKT_LIB_H__
#define __GRSPW_PKT_LIB_H__

#include <bsp/grspw_pkt.h>

/* GRSPW Device handles and DMA handles */
struct grspw_dev {
	void *dh;
	void *dma[4];
	int index;
	struct grspw_hw_sup hwsup;
};

/* Driver configuration options described in memory */
struct grspw_config {
	struct grspw_addr_config adrcfg;
	int rmap_cfg;
	unsigned char rmap_dstkey;
	int tc_cfg;
	void (*tc_isr_callback)(void *data, int tc);
	void *tc_isr_arg;
	/* Mask of which DMA Channels to enable. Most often only
	 * one DMA Channel is available, then set this to 1.
	 *
	 * By enabling a DMA Channel, the DMA Channels will be
	 * able to receive SpaceWire packets after SpaceWire buffers 
	 * has been prepared for it, and transmitt SpaceWire packets
	 * when the user request transmission of a SpaceWire packet.
	 */
	unsigned int enable_chan_mask;
	/* Per Channel Configuration */
	struct grspw_dma_config chan[4];
	/* SpW Interrupt configuration */
	struct spwpkt_ic_config iccfg;
};

/* Statisics and diagnostics gathered by driver */
struct grspw_stats {
	/* Statistics for the Core */
	struct grspw_core_stats stats;

	/* Per DMA channel statistics */
	struct grspw_dma_stats chan[4];
};

/* Current state of configuration and link */
struct grspw_link_state {
	int link_ctrl;			/* Link Configuration */
	unsigned char clkdiv_start;	/* Clock Division during startup (not 
					 * in state run) */
	unsigned char clkdiv_run;	/* Clock Division in run-state */
	spw_link_state_t link_state;	/* State (Error-Reset, Error-wait...) */
	int port_cfg;			/* Port Configuration */
	int port_active;		/* Currently active port */
};

/* Read the current driver configuration to memory */
void grspw_config_read(struct grspw_dev *dev, struct grspw_config *cfg);

/* Read the current link state from hardware */
void grspw_link_state_get(struct grspw_dev *dev, struct grspw_link_state *state);

/* Print the link state on the stdout */
void grspw_linkstate_print(struct grspw_link_state *ls);

/* Print hardware configuration from memory onto stdout */
void grspw_cfg_print(struct grspw_hw_sup *hw, struct grspw_config *cfg);

/* Copy current driver statistics to memory */
void grspw_stats_get(struct grspw_dev *dev, struct grspw_stats *stats);

/* Print GRSPW driver statistics from memory description onto stdout */
void grspw_stats_print(struct grspw_dev *dev, struct grspw_stats *stats);

/* Configure Core and DMA Channels, RMAP and TimeCode setup */
int grspw_cfg_set(struct grspw_dev *dev, struct grspw_config *cfg);

/* Start DMA operation on all open DMA channels */
int grspw_start(struct grspw_dev *dev);

/* Stop all DMA activity on all DMA channels */
void grspw_stop(struct grspw_dev *dev);

#endif /* __GRSPW_PKT_LIB_H__ */
