#include <stdio.h>
#include <string.h>
#include <ambapp_ids.h>
#include <rtems.h>
#include "grspw_pkt_lib.h"

#ifdef SILENT
#define PRINTF(x...) 
#else
#define PRINTF(x...) printf(x)
#endif

void grspw_config_read(struct grspw_dev *dev, struct grspw_config *cfg)
{
	int i;
	int rmap_dstkey;

	cfg->adrcfg.promiscuous = -1;
	grspw_addr_ctrl(dev->dh, &cfg->adrcfg);

	cfg->rmap_cfg = -1;
	rmap_dstkey = -1;
	grspw_rmap_ctrl(dev->dh, &cfg->rmap_cfg, &rmap_dstkey);
	cfg->rmap_dstkey = rmap_dstkey;

	cfg->tc_cfg = -1;
	grspw_tc_ctrl(dev->dh, &cfg->tc_cfg);

	cfg->enable_chan_mask = 0;
	for (i=0; i<dev->hwsup.ndma_chans; i++) {
		if ( dev->dma[i] ) {
			cfg->enable_chan_mask |= 1 << i;
			grspw_dma_config_read(dev->dma[i], &cfg->chan[i]);
		}
	}
}

void grspw_link_state_get(struct grspw_dev *dev, struct grspw_link_state *state)
{
	int clkdiv;

	/* Get Current Link Configuration */
	state->link_ctrl = -1;
	clkdiv = -1;
	grspw_link_ctrl(dev->dh, &state->link_ctrl, NULL, &clkdiv);
	state->clkdiv_start = (clkdiv >> 8) & 0xff;
	state->clkdiv_run = clkdiv & 0xff;

	/* Get Current Link Status */
	state->link_state = grspw_link_state(dev->dh);

	/* Get Current Port configuration */
	state->port_cfg = -1;
	grspw_port_ctrl(dev->dh, &state->port_cfg);

	/* Get Current Active port */
	state->port_active = grspw_port_active(dev->dh);
}

void grspw_linkstate_print(struct grspw_link_state *ls)
{
	PRINTF(" link_ctrl:      0x%02x\n", ls->link_ctrl);
	PRINTF(" clkdiv_start:   0x%02x\n", ls->clkdiv_start);
	PRINTF(" clkdiv_run:     0x%02x\n", ls->clkdiv_run);
	PRINTF(" link_state:     %d\n", ls->link_state);
	PRINTF(" port_cfg:       %d\n", ls->port_cfg);
	PRINTF(" port_active:    Port%d\n", ls->port_active);
}

void grspw_cfg_print(struct grspw_hw_sup *hw, struct grspw_config *cfg)
{
	int i;
	char *name;

	PRINTF("HARDWARE SUPPORT:\n");
	PRINTF(" RMAP:                    %s\n", hw->rmap ? "YES" : "NO");
	PRINTF(" RMAP CRC:                %s\n", hw->rmap_crc ? "YES" : "NO");
	PRINTF(" UNALIGNED RX ADR:        %s\n", hw->rx_unalign ? "YES" : "NO");
	PRINTF(" NUMBER OF PORTS:         %d\n", hw->nports);
	PRINTF(" DMA CHANNEL COUNT:       %d\n", hw->ndma_chans);
	i = hw->hw_version >> 16;
	switch (i) {
		case GAISLER_SPW: name = "GRSPW1"; break;
		case GAISLER_SPW2: name = "GRSPW2"; break;
		case GAISLER_SPW2_DMA: name = "ROUTER-GRSPW2"; break;
		default: name = "unknown";
	}
	PRINTF(" HARDWARE VERSION:        0x%08x %s\n", hw->hw_version, name);

	if (cfg == NULL)
		return;

	PRINTF("SOFTWARE CONFIGURATION:\n");
	PRINTF(" Promiscuous Mode:        %s\n", cfg->adrcfg.promiscuous ? "YES" : "NO");
	PRINTF(" Default Node Address:    0x%02x\n", cfg->adrcfg.def_addr);
	PRINTF(" Default Node Mask:       0x%02x\n", cfg->adrcfg.def_mask);
	for (i=0; i<hw->ndma_chans; i++) {
		PRINTF("  DMA[%d] NODE ADR EN:     %s\n", i, cfg->adrcfg.dma_nacfg[i].node_en ? "YES" : "NO");
		PRINTF("  DMA[%d] NODE ADDR:       0x%02x\n", i, cfg->adrcfg.dma_nacfg[i].node_addr);
		PRINTF("  DMA[%d] NODE MASK:       0x%02x\n", i, cfg->adrcfg.dma_nacfg[i].node_mask);
	}
	PRINTF(" RMAP ENABLED:            %s\n", cfg->rmap_cfg & RMAPOPTS_EN_RMAP ? "YES" : "NO");
	PRINTF(" RMAP BUFFER ENABLED:     %s\n", cfg->rmap_cfg & RMAPOPTS_EN_BUF ? "YES" : "NO");
	PRINTF(" RMAP DESTKEY:            0x%02x\n", cfg->rmap_dstkey);
	PRINTF(" TIMECODE RX ENABLED:     %s\n", cfg->tc_cfg & TCOPTS_EN_RX ? "YES" : "NO");
	PRINTF(" TIMECODE RX IRQ:         %s\n", cfg->tc_cfg & TCOPTS_EN_RXIRQ ? "YES" : "NO");
	PRINTF(" TIMECODE TX ENABLED:     %s\n", cfg->tc_cfg & TCOPTS_EN_TX ? "YES" : "NO");
	PRINTF(" DMA CHAN MASK ENABLE:    0x%02x\n", cfg->enable_chan_mask);	
	for (i=0; i<hw->ndma_chans; i++) {
		if ( (cfg->enable_chan_mask & (1<<i)) == 0 )
			continue;
		printf("  DMA[%d] FLAGS:           0x%08x (RXIRQ %s, TXIRQ %s)\n", i, cfg->chan[i].flags,
			cfg->chan[i].flags & DMAFLAG2_RXIE ? "ENABLED" : "DISABLED",
			cfg->chan[i].flags & DMAFLAG2_TXIE ? "ENABLED" : "DISABLED");
		PRINTF("  DMA[%d] RX MAX PKTLEN:   %d Bytes\n", i, cfg->chan[i].rxmaxlen);
		if ( cfg->chan[i].rx_irq_en_cnt == 0 )
			PRINTF("  DMA[%d] RX IRQ EN CNT:   IRQ DISABLED\n", i);
		else
			PRINTF("  DMA[%d] RX IRQ EN CNT:   1 IRQ per %d pkts\n", i, cfg->chan[i].rx_irq_en_cnt);
		if ( cfg->chan[i].tx_irq_en_cnt == 0 )
			PRINTF("  DMA[%d] TX IRQ EN CNT:   IRQ DISABLED\n", i);
		else
			PRINTF("  DMA[%d] TX IRQ EN CNT:   1 IRQ per %d pkts\n", i, cfg->chan[i].tx_irq_en_cnt);
	}
	fflush(NULL);
}

void grspw_stats_get(struct grspw_dev *dev, struct grspw_stats *stats)
{
	int i;

	grspw_stats_read(dev->dh, &stats->stats);

	for (i=0; i<dev->hwsup.ndma_chans; i++) {
		if ( dev->dma[i] )
			grspw_dma_stats_read(dev->dma[i], &stats->chan[i]);
		else
			memset(&stats->chan[i], 0, sizeof(struct grspw_dma_stats));
	}
}

void grspw_stats_print(struct grspw_dev *dev, struct grspw_stats *stats)
{
	int i;
	struct grspw_dma_stats *chan;

	PRINTF("SpW%d STATISTICS:\n", dev->index);
	PRINTF(" irq_cnt:                  %d\n", stats->stats.irq_cnt);
	PRINTF(" err_credit:               %d\n", stats->stats.err_credit);
	PRINTF(" err_eeop:                 %d\n", stats->stats.err_eeop);
	PRINTF(" err_addr:                 %d\n", stats->stats.err_addr);
	PRINTF(" err_parity:               %d\n", stats->stats.err_parity);
	printf(" err_disconnect:           %d\n", stats->stats.err_disconnect);
	PRINTF(" err_escape:               %d\n", stats->stats.err_escape);
	PRINTF(" err_wsync:                %d\n", stats->stats.err_wsync);

	for (i=0; i<dev->hwsup.ndma_chans; i++) {
		chan = &stats->chan[i];
		if (dev->dma[i] == NULL)
			continue;
		PRINTF(" DMA[%d] irq_cnt:           %d\n", i, chan->irq_cnt);
		PRINTF(" DMA[%d] tx_pkts:           %d\n", i, chan->tx_pkts);
		PRINTF(" DMA[%d] tx_err_link:       %d\n", i, chan->tx_err_link);
		PRINTF(" DMA[%d] rx_pkts:           %d\n", i, chan->rx_pkts);
		PRINTF(" DMA[%d] rx_err_trunk:      %d\n", i, chan->rx_err_trunk);
		PRINTF(" DMA[%d] rx_err_endpkt:     %d\n", i, chan->rx_err_endpkt);
		PRINTF(" DMA[%d] send_cnt_min:      %d\n", i, chan->send_cnt_min);
		PRINTF(" DMA[%d] send_cnt_max:      %d\n", i, chan->send_cnt_max);
		PRINTF(" DMA[%d] tx_sched_cnt_min:  %d\n", i, chan->tx_sched_cnt_min);
		PRINTF(" DMA[%d] tx_sched_cnt_max:  %d\n", i, chan->tx_sched_cnt_max);
		PRINTF(" DMA[%d] sent_cnt_max:      %d\n", i, chan->sent_cnt_max);
		PRINTF(" DMA[%d] ready_cnt_min:     %d\n", i, chan->ready_cnt_min);
		PRINTF(" DMA[%d] ready_cnt_max:     %d\n", i, chan->ready_cnt_max);
		PRINTF(" DMA[%d] rx_sched_cnt_min:  %d\n", i, chan->rx_sched_cnt_min);
		PRINTF(" DMA[%d] rx_sched_cnt_max:  %d\n", i, chan->rx_sched_cnt_max);
		PRINTF(" DMA[%d] recv_cnt_max:      %d\n", i, chan->recv_cnt_max);
		PRINTF(" DMA[%d] tx_work_cnt:       %d\n", i, chan->tx_work_cnt);
		PRINTF(" DMA[%d] rx_work_cnt:       %d\n", i, chan->rx_work_cnt);
		PRINTF(" DMA[%d] tx_work_enabled:   %d\n", i, chan->tx_work_enabled);
		PRINTF(" DMA[%d] rx_work_enabled:   %d\n", i, chan->rx_work_enabled);
	}
}

/* Configure Core and DMA Channels, RMAP and TimeCode setup */
int grspw_cfg_set(struct grspw_dev *dev, struct grspw_config *cfg)
{
	int rmap_dstkey;
	int i, retval;

	/* Check RMAP Configuration */
	if ( cfg->rmap_cfg & ~(RMAPOPTS_EN_RMAP|RMAPOPTS_EN_BUF) )
		return -1;

	/* Check Timecode Configuration, enabling RX IRQ not allowed from here */
	if ( cfg->tc_cfg & ~(TCOPTS_EN_RX|TCOPTS_EN_TX) )
		return -1;

	/* Check Channel Enable Mask, report error if trying to enable a 
	 * channel that is not available. */
	if ( (-1 << dev->hwsup.ndma_chans) & cfg->enable_chan_mask )
		return -1;

	/* 1. Configure Node address and Node mask of DMA Channels
	 *    and default node address of core itself.
	 */
	cfg->adrcfg.promiscuous &= 1;
	grspw_addr_ctrl(dev->dh, &cfg->adrcfg);

	/* 2. Configure RMAP (Enable, Buffer, Destination Key) */
	rmap_dstkey = cfg->rmap_dstkey;
	if ( grspw_rmap_ctrl(dev->dh, &cfg->rmap_cfg, &rmap_dstkey) ) {
		/* RMAP not available in Core, but trying to enable */
		return -2;
	}

	/* 3. Timecode setup. If a custom timecode ISR callback handler is 
	 *    installed that routine is installed and RX IRQ is enabled.
	 */
	if ( cfg->tc_isr_callback ) {
		grspw_tc_isr(dev->dh, cfg->tc_isr_callback, cfg->tc_isr_arg);
		cfg->tc_cfg |= TCOPTS_EN_RXIRQ;
	}
	grspw_tc_ctrl(dev->dh, &cfg->tc_cfg);

	/* 4. Configure SpaceWire Interrupt support
	 */
	grspw_ic_config(dev->dh, 1, &cfg->iccfg);

	/* 5. Configure DMA Channels and remember which channels will be
	 *    used. Only the enabled channels will be activated and started
	 *    during the ioctl(START) operation.
	 */
	retval = 0;
	for (i=0; i<dev->hwsup.ndma_chans; i++) {
		/* Open or close DMA Channel */
		if ( cfg->enable_chan_mask & (1<<i) ) {
			/* Should be opened */
			if ( dev->dma[i] == NULL ) {
				dev->dma[i] = grspw_dma_open(dev->dh, i);
				if ( dev->dma[i] == NULL ) {
					retval = -2;
					continue;
				}
			}

			/* Configure channel */
			grspw_dma_config(dev->dma[i], &cfg->chan[i]);
		} else {
			/* Should be closed */
			if ( dev->dma[i] ) {
				grspw_dma_close(dev->dma[i]);
				dev->dma[i] = NULL;
			}
		}
	}

	return retval;
}

void grspw_stop(struct grspw_dev *dev)
{
	int i;

	/* Stop all opened DMA channels */
	for (i=0; i<dev->hwsup.ndma_chans; i++) {
		if (dev->dma[i])
			grspw_dma_stop(dev->dma[i]);
	}
}

int grspw_start(struct grspw_dev *dev)
{
	int i;

	/* START all Channels for DMA operations */
	for (i=0; i<dev->hwsup.ndma_chans; i++) {
		if ( dev->dma[i] ) {
			if ( grspw_dma_start(dev->dma[i]) ) {
				/* Failed to start DMA channel */
				grspw_stop(dev);
				return -1;
			}
		}
	}

	return 0;
}
